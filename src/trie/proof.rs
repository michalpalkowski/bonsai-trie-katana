//! Merkle proof verification and generation for the Bonsai Trie.
//!
//! This module provides functionality for generating and verifying Merkle proofs
//! for the Bonsai Trie data structure. It includes:
//! - Multi-proof generation and verification
//! - Proof node types (Binary and Edge)
//! - Error handling for proof verification
//! - Utilities for calculating new root hashes

use super::{
    merkle_node::{hash_binary_node, hash_edge_node, Direction},
    path::Path,
    tree::{MerkleTree, ProofNodeChildren},
};
use crate::{
    id::Id,
    key_value_db::KeyValueDB,
    trie::{
        iterator::{NodeVisitor, PartialNodeVisitor},
        merkle_node::{Node, NodeHandle},
        tree::{NodeKey, RootHandle},
    },
    BitSlice, BitVec, BonsaiDatabase, BonsaiStorageError, HashMap, HashSet,
};
use core::{marker::PhantomData, mem, ops::DerefMut};
use hashbrown::hash_set;
use starknet_types_core::{felt::Felt, hash::StarkHash};

#[derive(Debug, thiserror::Error)]
pub enum ProofVerificationError {
    #[error("Key length mismatch: key {path:b}, expected length {expected}, got {got}")]
    KeyLengthMismatch {
        path: BitVec,
        expected: u8,
        got: usize,
    },
    #[error("Missing node in proof: key {path:b}, hash {hash:#x}")]
    MissingNode { path: BitVec, hash: Felt },
    #[error(
        "Overshot the expected path: path {path:b}, expected max height {expected_max_height}"
    )]
    Overshot {
        path: BitVec,
        expected_max_height: u8,
    },
    #[error("Node hash mismatch: path {path:b}, expected {expected:#x}, got {got:#x}")]
    HashMismatch {
        path: BitVec,
        expected: Felt,
        got: Felt,
    },
    #[error("Invalid proof")]
    InvalidProof,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ProofNode {
    Binary { left: Felt, right: Felt },
    Edge { child: Felt, path: Path },
}

impl ProofNode {
    pub fn hash<H: StarkHash>(&self) -> Felt {
        match self {
            ProofNode::Binary { left, right } => hash_binary_node::<H>(*left, *right),
            ProofNode::Edge { child, path } => hash_edge_node::<H>(path, *child),
        }
    }
}

#[derive(Debug, Clone)]
pub struct PartialPath(pub HashMap<NodeKey, (ProofNode, ProofNodeChildren)>);
#[derive(Debug, Clone)]
pub struct MultiProof(pub HashMap<Felt, ProofNode>);
impl MultiProof {
    /// If the proof proves more than just the provided `key_values`, this function will not fail.
    /// Not the most optimized way of doing it, but we don't actually need to verify proofs in madara.
    /// As such, it has also not been properly proptested.
    ///
    /// Returns an iterator of the values. Felt::ZERO is returned when the key is not a member of the trie.
    /// Do not forget to check the values returned by the iterator :)
    pub fn verify_proof<'a, 'b: 'a, H: StarkHash>(
        &'b self,
        root: Felt,
        key_values: impl IntoIterator<Item = impl AsRef<BitSlice>> + 'a,
        tree_height: u8,
    ) -> impl Iterator<Item = Result<Felt, ProofVerificationError>> + 'a {
        let mut checked_cache: HashSet<Felt> = Default::default();
        let mut current_path = BitVec::with_capacity(251);
        key_values.into_iter().map(move |k| {
            let k = k.as_ref();

            if k.len() != tree_height as usize {
                return Err(ProofVerificationError::KeyLengthMismatch {
                    path: k.into(),
                    expected: tree_height,
                    got: k.len(),
                });
            }

            // Go down the tree, starting from the root
            current_path.clear(); // hoisted alloc
            let mut current_felt = root;

            loop {
                log::trace!("Start verify loop: {current_path:b} => {current_felt:#x}");
                if current_path.len() == k.len() {
                    // End of traversal, return value
                    log::trace!("End of traversal");
                    return Ok(current_felt);
                }
                if current_path.len() > k.len() {
                    // We overshot.
                    log::trace!("Overshot");
                    return Err(ProofVerificationError::Overshot {
                        path: mem::take(&mut current_path),
                        expected_max_height: tree_height,
                    });
                }
                let Some(node) = self.0.get(&current_felt) else {
                    // Missing node.
                    log::trace!("Missing");
                    return Err(ProofVerificationError::MissingNode {
                        path: mem::take(&mut current_path),
                        hash: current_felt,
                    });
                };

                // Check hash and save to verification cache.
                if let hash_set::Entry::Vacant(entry) = checked_cache.entry(current_felt) {
                    let computed_hash = node.hash::<H>();
                    if computed_hash != current_felt {
                        // Hash mismatch.
                        log::trace!("Hash mismatch: {computed_hash:#x} {current_felt:#x}");
                        return Err(ProofVerificationError::HashMismatch {
                            expected: current_felt,
                            got: computed_hash,
                            path: mem::take(&mut current_path),
                        });
                    }
                    entry.insert();
                }

                match node {
                    ProofNode::Binary { left, right } => {
                        // PANIC: We checked above that current_path.len() < k.len().
                        let direction = Direction::from(k[current_path.len()]);
                        log::trace!("Binary {direction:?}");
                        current_path.push(direction.into());
                        current_felt = match direction {
                            Direction::Left => *left,
                            Direction::Right => *right,
                        }
                    }
                    ProofNode::Edge { child, path } => {
                        log::trace!("Edge");
                        if k.get(current_path.len()..(current_path.len() + path.len()))
                            != Some(&path.0)
                        {
                            log::trace!("Wrong edge: {path:?}");
                            // Wrong edge path: that's a non-membership proof.
                            return Ok(Felt::ZERO);
                        }
                        current_path.extend_from_bitslice(&path.0);
                        current_felt = *child;
                    }
                }
            }
        })
    }
}

impl<H: StarkHash + Send + Sync> MerkleTree<H> {
    /// This function is designed to be very efficient if the `keys` are sorted - this allows for
    /// the minimal amount of backtracking when switching from one key to the next.
    pub fn get_multi_proof<DB: BonsaiDatabase, ID: Id>(
        &mut self,
        db: &KeyValueDB<DB, ID>,
        keys: impl IntoIterator<Item = impl AsRef<BitSlice>>,
    ) -> Result<MultiProof, BonsaiStorageError<DB::DatabaseError>> {
        let max_height = self.max_height;

        struct ProofVisitor<H>(MultiProof, PhantomData<H>);
        impl<H: StarkHash + Send + Sync> NodeVisitor<H> for ProofVisitor<H> {
            fn visit_node<DB: BonsaiDatabase>(
                &mut self,
                tree: &mut MerkleTree<H>,
                node_id: NodeKey,
                _prev_height: usize,
            ) -> Result<(), BonsaiStorageError<DB::DatabaseError>> {
                let proof_node = match tree.get_node_mut::<DB>(node_id)? {
                    Node::Binary(binary_node) => {
                        let (left, right) = (binary_node.left, binary_node.right);
                        ProofNode::Binary {
                            left: tree.get_or_compute_node_hash::<DB>(left)?,
                            right: tree.get_or_compute_node_hash::<DB>(right)?,
                        }
                    }
                    Node::Edge(edge_node) => {
                        let (child, path) = (edge_node.child, edge_node.path.clone());
                        ProofNode::Edge {
                            child: tree.get_or_compute_node_hash::<DB>(child)?,
                            path,
                        }
                    }
                };
                let hash = tree.get_or_compute_node_hash::<DB>(NodeHandle::InMemory(node_id))?;
                self.0 .0.insert(hash, proof_node);
                Ok(())
            }
        }
        let mut visitor = ProofVisitor::<H>(MultiProof(Default::default()), PhantomData);

        let mut iter = self.iter(db);
        for key in keys {
            let key = key.as_ref();
            if key.len() != max_height as usize {
                return Err(BonsaiStorageError::KeyLength {
                    expected: self.max_height as _,
                    got: key.len(),
                });
            }
            iter.traverse_to(&mut visitor, key)?;
        }

        Ok(visitor.0)
    }

    pub fn get_partial_path<DB: BonsaiDatabase, ID: Id>(
        &mut self,
        db: &KeyValueDB<DB, ID>,
        keys: impl IntoIterator<Item = impl AsRef<BitSlice>>,
        full_proof: MultiProof,
        root: Felt,
    ) -> Result<(PartialPath, Vec<(NodeKey, usize)>), BonsaiStorageError<DB::DatabaseError>> {
        let max_height = self.max_height;
        let keys: Vec<_> = keys.into_iter().collect();

        struct PartialTrieVisitor<H>(PartialPath, PhantomData<H>);
        impl<H: StarkHash + Send + Sync> PartialNodeVisitor<H> for PartialTrieVisitor<H> {
            fn visit_partial_node<DB: BonsaiDatabase>(
                &mut self,
                tree: &mut MerkleTree<H>,
                node_id: NodeKey,
                _prev_height: usize,
            ) -> Result<(), BonsaiStorageError<DB::DatabaseError>> {
                let (proof_node, children) = tree.get_proof_node_mut::<DB>(node_id)?;
                self.0
                     .0
                    .insert(node_id, (proof_node.clone(), children.clone()));
                Ok(())
            }
        }

        let mut visitor = PartialTrieVisitor::<H>(PartialPath(HashMap::new()), PhantomData);
        let mut iter = self.iter_partial(db, full_proof);

        for key in keys {
            let key = key.as_ref();
            if key.len() != max_height as usize {
                return Err(BonsaiStorageError::KeyLength {
                    expected: self.max_height as _,
                    got: key.len(),
                });
            }
            iter.traverse_to_partial(&mut visitor, key, root)?;
        }
        let path_nodes = iter.current_partial_nodes_heights;
        Ok((visitor.0, path_nodes))
    }

    /// Calculates the next root hash after updating a value.
    ///
    /// # Arguments
    ///
    /// * `db` - The database to read nodes from
    /// * `key` - The key to update
    /// * `new_value` - The new value to set
    /// * `current_root` - The current root hash
    /// * `proof` - The proof for the key
    ///
    /// # Returns
    ///
    /// The new root hash after the update.
    pub fn next_root<DB: BonsaiDatabase, K: AsRef<BitSlice>>(
        &mut self,
        key: K,
        new_value: Felt,
        current_root: Felt,
        proof: &MultiProof,
    ) -> Result<Felt, BonsaiStorageError<DB::DatabaseError>> {
        let mut current_path = BitVec::with_capacity(251);
        let mut current_felt = current_root;
        let mut path_nodes = Vec::new();

        loop {
            if current_path.len() == key.as_ref().len() {
                break;
            }

            let Some(node) = proof.0.get(&current_felt) else {
                break;
            };

            path_nodes.push((current_path.clone(), node.clone()));

            match node {
                ProofNode::Binary { left, right } => {
                    let direction = Direction::from(key.as_ref()[current_path.len()]);
                    current_path.push(direction.into());
                    current_felt = match direction {
                        Direction::Left => *left,
                        Direction::Right => *right,
                    };
                }
                ProofNode::Edge { child, path } => {
                    if key
                        .as_ref()
                        .get(current_path.len()..(current_path.len() + path.len()))
                        != Some(&path.0)
                    {
                        break;
                    }
                    current_path.extend_from_bitslice(&path.0);
                    current_felt = *child;
                }
            }
        }

        calculate_new_root_hash::<H, DB>(key.as_ref(), new_value, &path_nodes)
    }
}

/// Calculates the new root hash after updating a value.
///
/// # Arguments
///
/// * `key` - The key being updated
/// * `new_value` - The new value to set
/// * `path_nodes` - The nodes along the path to the key
///
/// # Returns
///
/// The new root hash after the update.
pub fn calculate_new_root_hash<H: StarkHash, DB: BonsaiDatabase>(
    key: &BitSlice,
    new_value: Felt,
    path_nodes: &[(BitVec, ProofNode)],
) -> Result<Felt, BonsaiStorageError<DB::DatabaseError>> {
    match path_nodes.last() {
        Some((
            edge_path_vec,
            ProofNode::Edge {
                child,
                path: edge_path,
            },
        )) => {
            let edge_height = edge_path_vec.len();
            let common = common_path(edge_path, edge_height, key);
            let branch_height = edge_height + common.len();

            if branch_height >= key.len() {
                return Ok(hash_up_merkle_path::<H>(key, new_value, path_nodes, false));
            }

            // Create a new binary node at the divergence point
            let child_height = branch_height + 1;
            let new_path = key[child_height..].to_bitvec();
            let old_path = edge_path.0[common.len() + 1..].to_bitvec();

            let new_leaf_hash = new_value;
            let old_leaf_hash = *child;

            let new = if new_path.is_empty() {
                new_leaf_hash
            } else {
                hash_edge_node::<H>(&Path(new_path), new_leaf_hash)
            };
            let old = if old_path.is_empty() {
                old_leaf_hash
            } else {
                hash_edge_node::<H>(&Path(old_path), old_leaf_hash)
            };

            let new_direction = Direction::from(key[branch_height]);
            let branch_hash = match new_direction {
                Direction::Left => hash_binary_node::<H>(new, old),
                Direction::Right => hash_binary_node::<H>(old, new),
            };

            let current_hash = if common.is_empty() {
                branch_hash
            } else {
                hash_edge_node::<H>(&Path(edge_path.0[..common.len()].to_bitvec()), branch_hash)
            };

            let current_hash = hash_up_merkle_path::<H>(key, current_hash, path_nodes, true);

            Ok(current_hash)
        }
        Some((path, ProofNode::Binary { left, right })) => {
            let direction = Direction::from(key[path.len()]);
            let current_hash = match direction {
                Direction::Left => hash_binary_node::<H>(new_value, *right),
                Direction::Right => hash_binary_node::<H>(*left, new_value),
            };

            let current_hash = hash_up_merkle_path::<H>(key, current_hash, path_nodes, true);

            Ok(current_hash)
        }
        None => {
            let final_hash = hash_edge_node::<H>(&Path(key.to_bitvec()), new_value);
            Ok(final_hash)
        }
    }
}

/// Finds the common prefix between an edge path and a key.
///
/// # Arguments
///
/// * `edge_path` - The path of the edge node
/// * `edge_height` - The height of the edge node
/// * `key` - The key to compare against
///
/// # Returns
///
/// The common prefix between the edge path and the key.
pub fn common_path<'a>(edge_path: &'a Path, edge_height: usize, key: &BitSlice) -> &'a BitSlice {
    let key_path = key.iter().skip(edge_height);
    let common_length = key_path
        .zip(edge_path.0.iter())
        .take_while(|(a, b)| a == b)
        .count();
    &edge_path.0[..common_length]
}

/// Hashes up the Merkle path from a leaf to the root.
///
/// # Arguments
///
/// * `key` - The key being updated
/// * `current_hash` - The current hash at the leaf
/// * `path_nodes` - The nodes along the path
/// * `skip_last` - Whether to skip the last node in the path
///
/// # Returns
///
/// The new root hash.
pub fn hash_up_merkle_path<H: StarkHash>(
    key: &BitSlice,
    mut current_hash: Felt,
    path_nodes: &[(BitVec, ProofNode)],
    skip_last: bool, // whether to skip the last element (e.g. if you've already processed it)
) -> Felt {
    let iter = if skip_last {
        path_nodes.iter().rev().skip(1)
    } else {
        path_nodes.iter().rev().skip(0)
    };
    for (path, node) in iter {
        match node {
            ProofNode::Binary { left, right } => {
                let direction = Direction::from(key[path.len()]);
                current_hash = match direction {
                    Direction::Left => hash_binary_node::<H>(current_hash, *right),
                    Direction::Right => hash_binary_node::<H>(*left, current_hash),
                };
            }
            ProofNode::Edge {
                path: edge_path, ..
            } => {
                current_hash = hash_edge_node::<H>(edge_path, current_hash);
            }
        }
    }
    current_hash
}

#[cfg(test)]
mod tests {
    use crate::{
        databases::{create_rocks_db, RocksDB, RocksDBConfig},
        id::BasicId,
        BonsaiStorage, BonsaiStorageConfig,
    };
    use bitvec::{bits, order::Msb0};
    use starknet_types_core::{felt::Felt, hash::Pedersen};

    const ZERO: Felt = Felt::ZERO;
    const ONE: Felt = Felt::ONE;
    const TWO: Felt = Felt::TWO;
    const THREE: Felt = Felt::THREE;
    const FOUR: Felt = Felt::from_hex_unchecked("0x4");

    #[test]
    fn test_multiproof() {
        let _ = env_logger::builder().is_test(true).try_init();
        log::set_max_level(log::LevelFilter::Trace);
        let tempdir = tempfile::tempdir().unwrap();
        let db = create_rocks_db(tempdir.path()).unwrap();
        let mut bonsai_storage: BonsaiStorage<BasicId, _, Pedersen> = BonsaiStorage::new(
            RocksDB::<BasicId>::new(&db, RocksDBConfig::default()),
            BonsaiStorageConfig::default(),
            8,
        );

        let key_values = [
            (bits![u8, Msb0; 0,0,0,1,0,0,0,0], ONE),
            (bits![u8, Msb0; 0,0,0,1,0,0,0,1], TWO),
            (bits![u8, Msb0; 0,0,0,1,1,1,0,1], ZERO),
            (bits![u8, Msb0; 1,0,0,1,0,0,0,1], ZERO),
            (bits![u8, Msb0; 0,1,1,1,1,1,0,1], THREE),
            (bits![u8, Msb0; 0,0,0,1,0,0,1,0], ZERO),
            (bits![u8, Msb0; 0,1,0,0,0,0,0,0], FOUR),
            (bits![u8, Msb0; 1,0,0,1,0,1,0,1], ZERO),
        ];

        for (k, v) in key_values.iter() {
            bonsai_storage.insert(&[], k, v).unwrap();
        }

        bonsai_storage.dump();

        let tree = bonsai_storage
            .tries
            .trees
            .get_mut(&smallvec::smallvec![])
            .unwrap();

        let proof = tree
            .get_multi_proof(&bonsai_storage.tries.db, key_values.iter().map(|(k, _v)| k))
            .unwrap();

        log::trace!("proof: {proof:?}");
        assert_eq!(
            proof
                .verify_proof::<Pedersen>(
                    tree.root_hash(&bonsai_storage.tries.db).unwrap(),
                    key_values.iter().map(|(k, _v)| k),
                    8
                )
                .collect::<Result<Vec<_>, _>>()
                .unwrap(),
            key_values.iter().map(|(_k, v)| *v).collect::<Vec<_>>()
        );
    }
}

#[should_panic(expected = "The tree has uncommited changes")]
#[test]
fn test_if_uncommited_changes_fails() {
    use crate::{
        databases::{create_rocks_db, RocksDB, RocksDBConfig},
        id::{BasicId, BasicIdBuilder},
        BonsaiStorage, BonsaiStorageConfig,
    };
    use starknet_types_core::{felt::Felt, hash::Pedersen};

    let db = create_rocks_db(tempfile::tempdir().unwrap().path()).unwrap();
    let identifier1 = vec![1];

    let config = BonsaiStorageConfig::default();
    let mut bonsai_storage: BonsaiStorage<BasicId, RocksDB<'_, BasicId>, Pedersen> =
        BonsaiStorage::new(
            RocksDB::new(&db, RocksDBConfig::default()),
            config.clone(),
            24,
        );

    let mut id_builder = BasicIdBuilder::new();

    for i in 0..5 {
        let mut key = vec![0; 3];
        key[0] = i;
        let value = Felt::from(i as u64 + 100);
        bonsai_storage
            .insert(&identifier1, &BitVec::from_vec(key), &value)
            .unwrap();
    }

    // Test root hash before commit
    let root_result1 = bonsai_storage.root_hash(&identifier1).unwrap();

    // Commit changes and test root hash after commit
    bonsai_storage.commit(id_builder.new_id()).unwrap();
    let root_result2 = bonsai_storage.root_hash(&identifier1).unwrap();
}

#[test]
fn test_next_root() {
    use crate::{
        databases::{create_rocks_db, RocksDB, RocksDBConfig},
        id::{BasicId, BasicIdBuilder},
        BonsaiStorage, BonsaiStorageConfig,
    };
    use bitvec::prelude::Msb0;
    use starknet_types_core::{felt::Felt, hash::Pedersen};

    let db = create_rocks_db(tempfile::tempdir().unwrap().path()).unwrap();
    let identifier = vec![1];
    let identifier2 = vec![2];

    let config = BonsaiStorageConfig::default();
    let mut bonsai_storage1: BonsaiStorage<BasicId, RocksDB<'_, BasicId>, Pedersen> =
        BonsaiStorage::new(
            RocksDB::new(&db, RocksDBConfig::default()),
            config.clone(),
            24,
        );
    let mut bonsai_storage2: BonsaiStorage<BasicId, RocksDB<'_, BasicId>, Pedersen> =
        BonsaiStorage::new(
            RocksDB::new(&db, RocksDBConfig::default()),
            config.clone(),
            24,
        );

    let mut id_builder = BasicIdBuilder::new();

    // Insert some initial values into both trees
    for i in 0..5 {
        let mut key = vec![0; 3];
        key[0] = i;
        let value = Felt::from(i as u64 + 100);
        bonsai_storage1
            .insert(&identifier, &BitVec::from_vec(key.clone()), &value)
            .unwrap();
        bonsai_storage2
            .insert(&identifier2, &BitVec::from_vec(key), &value)
            .unwrap();
    }

    // Commit both trees
    let id1 = id_builder.new_id();
    bonsai_storage1.commit(id1).unwrap();
    let current_root = bonsai_storage1.root_hash(&identifier).unwrap();

    // Create a new key and value to insert
    let mut new_key = vec![0; 3];
    new_key[0] = 5;
    let new_value = Felt::from(105);
    let new_key_bv = BitVec::from_vec(new_key.clone());

    // Get the tree from bonsai_storage1
    let tree1 = bonsai_storage1
        .tries
        .trees
        .entry(smallvec::smallvec![1])
        .or_insert_with(|| MerkleTree::new(identifier.into(), 24));

    let proof_keys = vec![&new_key_bv];
    let proof = tree1
        .get_multi_proof(&bonsai_storage1.tries.db, proof_keys.iter())
        .unwrap();

    // Calculate next root using our function
    let next_root = tree1
        .next_root::<RocksDB<'_, BasicId>, &bitvec::vec::BitVec<u8, Msb0>>(
            &new_key_bv,
            new_value,
            current_root,
            &proof,
        )
        .unwrap();

    let id2 = id_builder.new_id();
    bonsai_storage2.commit(id2).unwrap();
    // Get current root hash
    let current_root2 = bonsai_storage2.root_hash(&identifier2).unwrap();

    // Actually insert the value into the second tree
    bonsai_storage2
        .insert(&identifier2, &new_key_bv, &new_value)
        .unwrap();
    bonsai_storage2.commit(id_builder.new_id()).unwrap();

    // Get the actual root hash after insertion
    let actual_root = bonsai_storage2.root_hash(&identifier2).unwrap();

    // Verify that our calculated next root matches the actual root
    assert_eq!(next_root, actual_root, "Next root calculation failed");
}

#[cfg(test)]
mod proof_proptest {
    use crate::trie::tree::MerkleTree;
    use crate::{
        databases::{create_rocks_db, RocksDB, RocksDBConfig},
        id::{BasicId, BasicIdBuilder},
        BitVec, BonsaiStorage, BonsaiStorageConfig,
    };
    use bitvec::prelude::Msb0;
    use proptest::collection::vec;
    use proptest::num::u8;
    use proptest::prelude::*;
    use starknet_types_core::{felt::Felt, hash::Pedersen};

    // Generator for random keys of given length
    fn arb_key(max_height: u8) -> impl Strategy<Value = BitVec> {
        prop::collection::vec(any::<bool>(), max_height as usize)
            .prop_map(|bits| bits.into_iter().collect())
    }

    fn arb_key_value(max_height: u8) -> impl Strategy<Value = (BitVec, Felt)> {
        (
            prop::collection::vec(any::<bool>(), max_height as usize),
            u8::ANY,
        )
            .prop_map(|(bits, v)| {
                let key = bits.into_iter().collect();
                let value = Felt::from(v as u64 + 100);
                (key, value)
            })
    }

    // Generator for random values
    fn arb_value() -> impl Strategy<Value = Felt> {
        u8::ANY.prop_map(|v| {
            let value = Felt::from(v as u64 + 100);
            value
        })
    }

    fn arb_power_of_two_keys(max_height: u8) -> impl Strategy<Value = Vec<(BitVec, Felt)>> {
        (0..8).prop_flat_map(move |power| {
            let num_keys = 1 << power;
            prop::collection::vec(arb_key_value(max_height), num_keys as usize)
        })
    }

    fn select_random_key_value_from_initial_keys(
        initial_keys_values: Vec<(BitVec, Felt)>,
    ) -> (BitVec, Felt, Vec<(BitVec, Felt)>) {
        let random_index = rand::random::<usize>() % initial_keys_values.len();
        let (removed_key, removed_value) = initial_keys_values[random_index].clone();

        // Create a new vector without the removed key-value pair
        let remaining_keys_values: Vec<(BitVec, Felt)> = initial_keys_values
            .into_iter()
            .enumerate()
            .filter(|(i, _)| *i != random_index)
            .map(|(_, kv)| kv)
            .collect();

        (removed_key, removed_value, remaining_keys_values)
    }

    proptest! {
        #![proptest_config(ProptestConfig::default())]
        #[test]
        fn test_next_root_height_8(
            initial_keys_values in arb_power_of_two_keys(8),
        ) {
            // Randomly select a key-value pair to remove and use as new_key/new_value
            let (removed_key, removed_value, remaining_keys_values) = select_random_key_value_from_initial_keys(initial_keys_values);
            test_next_root(8, remaining_keys_values, removed_key, removed_value);
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::default())]
        #[test]
        fn test_next_root_height_24(
            initial_keys_values in arb_power_of_two_keys(24),
        ) {
            // Randomly select a key-value pair to remove and use as new_key/new_value
            let (removed_key, removed_value, remaining_keys_values) = select_random_key_value_from_initial_keys(initial_keys_values);
            test_next_root(24, remaining_keys_values, removed_key, removed_value);
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::default())]
        #[test]
        fn test_next_root_height_251(
            initial_keys_values in vec(arb_key_value(251), 1..50), // minimum 1 key to ensure we can remove one
        ) {
            // Randomly select a key-value pair to remove and use as new_key/new_value
            let (removed_key, removed_value, remaining_keys_values) = select_random_key_value_from_initial_keys(initial_keys_values);
            test_next_root(251, remaining_keys_values, removed_key, removed_value);
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::default())]
        #[test]
        fn test_next_root_empty_initial(
            new_key in arb_key(8),
            new_value in arb_value(),
        ) {
            test_next_root(8, vec![], new_key, new_value);
        }
    }

    // Helper function to run the test
    fn test_next_root(
        height: u8,
        initial_keys_values: Vec<(BitVec, Felt)>,
        new_key: BitVec,
        new_value: Felt,
    ) {
        let db = create_rocks_db(tempfile::tempdir().unwrap().path()).unwrap();
        let identifier1 = vec![1];
        let identifier2 = vec![2];

        let config = BonsaiStorageConfig::default();
        let mut bonsai_storage1: BonsaiStorage<BasicId, RocksDB<'_, BasicId>, Pedersen> =
            BonsaiStorage::new(
                RocksDB::new(&db, RocksDBConfig::default()),
                config.clone(),
                height,
            );
        let mut bonsai_storage2: BonsaiStorage<BasicId, RocksDB<'_, BasicId>, Pedersen> =
            BonsaiStorage::new(
                RocksDB::new(&db, RocksDBConfig::default()),
                config.clone(),
                height,
            );

        let mut id_builder = BasicIdBuilder::new();

        // Insert initial values
        for (key, value) in initial_keys_values.iter() {
            bonsai_storage1.insert(&identifier1, key, value).unwrap();
            bonsai_storage2.insert(&identifier2, key, value).unwrap();
        }

        // Commit both trees
        let id1 = id_builder.new_id();
        bonsai_storage1.commit(id1).unwrap();

        // This has to be done before second tree commit
        let current_root = bonsai_storage1.root_hash(&identifier1).unwrap();
        // Get the tree from bonsai_storage1

        let tree1 = bonsai_storage1
            .tries
            .trees
            .entry(smallvec::smallvec![1])
            .or_insert_with(|| MerkleTree::new(identifier1.into(), height));

        // This has to be done before second tree commit
        let mut proof_keys = vec![&new_key];
        let proof = tree1
            .get_multi_proof(&bonsai_storage1.tries.db, proof_keys.iter())
            .unwrap();

        // Calculate next root using our function
        let next_root = tree1
            .next_root::<RocksDB<'_, BasicId>, &bitvec::vec::BitVec<u8, Msb0>>(
                &new_key,
                new_value,
                current_root,
                &proof,
            )
            .unwrap();

        let id2 = id_builder.new_id();
        bonsai_storage2.commit(id2).unwrap();
        let root2 = bonsai_storage2.root_hash(&identifier2).unwrap();
        assert_eq!(
            current_root, root2,
            "Roots should be equal after initial commit"
        );

        bonsai_storage2
            .insert(&identifier2, &new_key, &new_value)
            .unwrap();
        bonsai_storage2.commit(id_builder.new_id()).unwrap();

        // Get the actual root hash after insertion
        let actual_root = bonsai_storage2.root_hash(&identifier2).unwrap();

        // Verify that our calculated next root matches the actual root
        assert_eq!(next_root, actual_root,);
    }

    // Test next_root with specific edge cases
    #[test]
    fn test_next_root_specific_edge_cases() {
        let heights = [8, 24, 251];

        for height in heights {
            // Create a base key that will be used as initial key
            let mut base_key = BitVec::with_capacity(height as usize);
            for i in 0..height {
                base_key.push(i % 2 == 0);
            }
            let initial_keys_values = vec![(base_key.clone(), Felt::from(100))];

            // Case 1: Empty key (all zeros)
            let mut empty_key = BitVec::with_capacity(height as usize);
            for _ in 0..height {
                empty_key.push(false);
            }
            test_next_root(
                height,
                initial_keys_values.clone(),
                empty_key,
                Felt::from(100),
            );

            // Case 2: Full key (all ones)
            let mut full_key = BitVec::with_capacity(height as usize);
            for _ in 0..height {
                full_key.push(true);
            }
            test_next_root(
                height,
                initial_keys_values.clone(),
                full_key,
                Felt::from(200),
            );

            // Case 3: Alternating bits
            let mut alt_key = BitVec::with_capacity(height as usize);
            for i in 0..height {
                alt_key.push(i % 2 == 0);
            }
            test_next_root(
                height,
                initial_keys_values.clone(),
                alt_key,
                Felt::from(300),
            );

            // Case 4: Single bit set at different positions
            for pos in 0..height {
                let mut single_bit_key = BitVec::with_capacity(height as usize);
                for i in 0..height {
                    single_bit_key.push(i == pos);
                }
                test_next_root(
                    height,
                    initial_keys_values.clone(),
                    single_bit_key,
                    Felt::from(400 + pos as u64),
                );
            }

            // Case 5: Overwriting existing value
            let mut key = BitVec::with_capacity(height as usize);
            key.push(true);
            for _ in 1..height {
                key.push(false);
            }
            test_next_root(height, initial_keys_values.clone(), key, Felt::from(600));
        }
    }
}
