use super::{
    merkle_node::{hash_binary_node, hash_edge_node, Direction, EdgeNode},
    path::Path,
    tree::{MerkleTree, RootHandle},
};
use crate::trie::merkle_node::BinaryNode;
use crate::{
    id::Id,
    key_value_db::KeyValueDB,
    trie::{
        iterator::NodeVisitor,
        merkle_node::{Node, NodeHandle},
        tree::NodeKey,
    },
    BitSlice, BitVec, BonsaiDatabase, BonsaiStorageError, HashMap, HashSet,
};
use core::{marker::PhantomData, mem};
use hashbrown::hash_set;
use starknet_types_core::{
    felt::Felt,
    hash::{Poseidon, StarkHash},
};

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

            // Go down the tree, starting from the root.
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

    pub fn next_root<DB: BonsaiDatabase, ID: Id>(
        &mut self,
        db: &KeyValueDB<DB, ID>,
        key: &BitSlice,
        new_value: Felt,
    ) -> Result<Felt, BonsaiStorageError<DB::DatabaseError>> {
        // Get multiproof for the key (which doesn't exist yet)
        let proof_keys = vec![key.to_bitvec()];
        let proof = self.get_multi_proof(db, proof_keys.iter())?;
        println!("--------------------------------");
        println!("proof: {:?}", proof);
        println!("--------------------------------");

        let mut new_key = vec![0; 3];
        new_key[0] = 5;
        let new_test_value = Felt::from(500);
        let new_key_bv = BitVec::from_vec(new_key.clone());
        let test_keys = vec![new_key_bv];
        let test_proof = self.get_multi_proof(db, test_keys.iter())?;
        println!("--------------------------------");
        println!("Prooof for existing value 0: {:?}", test_proof);
        println!("--------------------------------");

        // Get current root hash
        let current_root = self.root_hash(db)?;
        println!("current_root: {:?}", current_root);

        // First pass: collect all nodes from the proof
        let mut current_path = BitVec::with_capacity(251);
        let mut current_felt = current_root;
        let mut path_nodes = Vec::new(); // Store nodes in path for building the tree

        loop {
            if current_path.len() == key.len() {
                // We've reached the leaf node
                println!("--------------------------------");
                println!("Reached leaf node");
                println!("current_path: {:?}", current_path);
                println!("current_felt: {:?}", current_felt);
                println!("--------------------------------");
                // Case 1: We've reached the leaf node - we'll replace its value
                break;
            }

            let Some(node) = proof.0.get(&current_felt) else {
                println!("--------------------------------");
                println!("Missing node in multiproof");
                println!("current_felt: {:?}", current_felt);
                println!("--------------------------------");
                // Case 2: Node not found in proof - we'll create a new path
                break;
            };

            // Store node and its path for later
            path_nodes.push((current_path.clone(), node.clone()));

            match node {
                ProofNode::Binary { left, right } => {
                    let direction = Direction::from(key[current_path.len()]);
                    println!("--------------------------------");
                    println!("Binary node");
                    println!("direction: {:?}", direction);
                    println!("current_path: {:?}", current_path);
                    println!("left: {:?}", left);
                    println!("right: {:?}", right);
                    println!("--------------------------------");
                    current_path.push(direction.into());
                    current_felt = match direction {
                        Direction::Left => *left,
                        Direction::Right => *right,
                    };
                }
                ProofNode::Edge { child, path } => {
                    if key.get(current_path.len()..(current_path.len() + path.len()))
                        != Some(&path.0)
                    {
                        // Case 3: Paths diverge - we'll create a binary node at divergence point
                        break;
                    }
                    current_path.extend_from_bitslice(&path.0);
                    current_felt = *child;
                }
            }
        }

        // Use calculate_new_root_hash to handle all cases:
        // 1. Replace existing leaf value
        // 2. Create new path when node not found
        // 3. Create binary node at divergence point
        calculate_new_root_hash::<H, DB>(key, new_value, &path_nodes)
    }
}

pub fn calculate_new_root_hash<H: StarkHash, DB: BonsaiDatabase>(
    key: &BitSlice,
    new_value: Felt,
    path_nodes: &Vec<(BitVec, ProofNode)>,
) -> Result<Felt, BonsaiStorageError<DB::DatabaseError>> {
    match path_nodes.last() {
        Some((
            edge_path_vec,
            ProofNode::Edge {
                child,
                path: edge_path,
            },
        )) => {
            println!("--------------------------------");
            println!("Edge node");
            println!("edge_path: {:?}", edge_path);
            println!("child: {:?}", child);
            println!("--------------------------------");
            let edge_height = edge_path_vec.len();
            let common = common_path(edge_path, edge_height, key);
            let branch_height = edge_height + common.len();

            if branch_height >= key.len() {
                println!("Reached end of key - replacing existing value");
                return Ok(hash_up_merkle_path::<H>(key, new_value, &path_nodes, false));
            }

            // Otherwise create a new binary node at the divergence point
            println!("Creating new binary node at height {}", branch_height);
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
            println!("--------------------------------");
            println!("Binary node");
            println!("path: {:?}", path);
            println!("left: {:?}", left);
            println!("right: {:?}", right);
            println!("--------------------------------");
            // If multiproof ends with a binary node (not edge)
            let direction = Direction::from(key[path.len()]);
            let current_hash = match direction {
                Direction::Left => hash_binary_node::<H>(new_value, *right),
                Direction::Right => hash_binary_node::<H>(*left, new_value),
            };

            let current_hash = hash_up_merkle_path::<H>(key, current_hash, path_nodes, true);

            Ok(current_hash)
        }
        None => {
            println!("--------------------------------");
            println!("No nodes in multiproof");
            println!("key: {:?}", key);
            println!("new_value: {:?}", new_value);
            println!("--------------------------------");
            let final_hash = hash_edge_node::<H>(&Path(key.to_bitvec()), new_value);
            Ok(final_hash)
        }
    }
}

pub fn common_path<'a>(edge_path: &'a Path, edge_height: usize, key: &BitSlice) -> &'a BitSlice {
    let key_path = key.iter().skip(edge_height);
    let common_length = key_path
        .zip(edge_path.0.iter())
        .take_while(|(a, b)| a == b)
        .count();
    &edge_path.0[..common_length]
}

pub fn hash_up_merkle_path<H: StarkHash>(
    key: &BitSlice,
    mut current_hash: Felt,
    path_nodes: &[(BitVec, ProofNode)],
    skip_last: bool, // czy pominąć ostatni element (np. jeśli już go przetworzyłeś)
) -> Felt {
    let iter = if skip_last {
        path_nodes.iter().rev().skip(1)
    } else {
        path_nodes.iter().rev().skip(0)
    };
    for (path, node) in iter {
        println!("--------------------------------");
        println!("Hashing up merkle path");
        println!("path: {:?}", path);
        println!("node: {:?}", node);
        println!("--------------------------------");
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
                current_hash = hash_edge_node::<H>(&edge_path, current_hash);
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

use crate::{BonsaiStorage, BonsaiStorageConfig};
use starknet_types_core::hash::Pedersen;

#[test]
fn test_merge_trees_multiproof_failure() {
    use crate::{
        databases::{create_rocks_db, RocksDB, RocksDBConfig, RocksDBTransaction},
        id::{BasicId, BasicIdBuilder},
        BonsaiStorage, BonsaiStorageConfig,
    };
    use bitvec::{bits, order::Msb0};
    use once_cell::sync::Lazy;
    use rocksdb::OptimisticTransactionDB;
    use starknet_types_core::{felt::Felt, hash::Pedersen};
    use std::sync::Arc;
    use std::sync::Mutex;

    let db = create_rocks_db(tempfile::tempdir().unwrap().path()).unwrap();
    let identifier1 = vec![1];
    let identifier2 = vec![2];
    let identifier3 = vec![3];

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
    let start_id = id_builder.new_id();
    bonsai_storage.commit(start_id).unwrap();
    //check if commit cahnges root

    // let mut bonsai_storage2 =
    //     BonsaiStorage::new(RocksDB::new(&db, RocksDBConfig::default()), config.clone(), 24);
    let mut bonsai_storage3: BonsaiStorage<BasicId, RocksDB<'_, BasicId>, Pedersen> =
        BonsaiStorage::new(
            RocksDB::new(&db, RocksDBConfig::default()),
            config.clone(),
            24,
        );

    // let mut txn_storage: BonsaiStorage<BasicId, RocksDBTransaction<'_>, Pedersen> = bonsai_storage
    // .get_transactional_state(start_id, config.clone())
    // .expect("Failed to get transactional state")
    // .expect("Transactional state not found");

    // let mut txn_storage = bonsai_storage.get_transactional_state(start_id, config.clone())
    // .expect("Transaction not found")
    // .expect("Transactional state not found");

    // for i in 5..15 {
    //     let mut key = vec![0; 3];
    //     key[0] = i;
    //     let value = Felt::from(i as u64 + 100);
    //     txn_storage.insert(&identifier2, &BitVec::from_vec(key), &value).unwrap();
    // }
    //check input permutation
    let id2 = id_builder.new_id();

    // bonsai_storage.merge(txn_storage).unwrap();

    let mut keys_and_values = Vec::new();
    for i in 5..15 {
        let mut key = vec![0; 3];
        key[0] = i;
        let value = Felt::from(i as u64 + 100);
        keys_and_values.push((key, value));
    }

    // bonsai_storage.merge_with_transaction(start_id, config.clone(), |txn_storage: &mut BonsaiStorage<BasicId, RocksDBTransaction<'_>, Pedersen>| {
    //     for (key, value) in keys_and_values {
    //         txn_storage.insert(&identifier2, &BitVec::from_vec(key), &value).unwrap();
    //     }
    // }).unwrap();

    // bonsai_storage.commit(id2).unwrap();

    // Fill third tree with all 15 elements (0-14) - original values
    for i in 0..15 {
        let mut key = vec![0; 3];
        key[0] = i;
        let value = Felt::from(i as u64 + 100);
        bonsai_storage3
            .insert(&identifier3, &BitVec::from_vec(key.clone()), &value)
            .unwrap();
    }
    let id3 = id_builder.new_id();
    bonsai_storage3.commit(id3).unwrap();

    // Check if keys are correctly visible in storage2 after merge
    println!("Checking keys after merge:");
    for i in 0..15 {
        let mut key = vec![0; 3];
        key[0] = i;
        let key = BitVec::from_vec(key);
        let val2 = bonsai_storage.get(&identifier2, &key).unwrap();
        let val3 = bonsai_storage3.get(&identifier3, &key).unwrap();
        println!("Key {}: storage2={:?}, storage3={:?}", i, val2, val3);
    }

    println!("Preparing keys for multi_proof");
    // Prepare keys for multi_proof
    let proof_keys: Vec<BitVec> = (0..15)
        .map(|i| {
            let mut key = vec![0; 3]; // 24-bit key (3 bytes)
            key[0] = i;
            BitVec::from_vec(key)
        })
        .collect();

    println!("Getting multi_proof for merged tree");
    // Get multi_proof for merged tree
    let merged_proof_result = bonsai_storage.get_multi_proof(&identifier2, &proof_keys);
    println!("Merged proof result: {:?}", merged_proof_result.is_ok());
    let merged_proof = match merged_proof_result {
        Ok(proof) => {
            println!(
                "Merged proof successfully retrieved, contains {} nodes",
                proof.0.len()
            );
            proof
        }
        Err(e) => {
            println!("Error while getting merged_proof: {:?}", e);
            panic!("Failed to get merged_proof");
        }
    };

    println!("Getting multi_proof for reference tree");
    // Get multi_proof for reference tree
    let reference_proof_result = bonsai_storage3.get_multi_proof(&identifier3, &proof_keys);
    println!(
        "Reference proof result: {:?}",
        reference_proof_result.is_ok()
    );
    let reference_proof = match reference_proof_result {
        Ok(proof) => {
            println!(
                "Reference proof successfully retrieved, contains {} nodes",
                proof.0.len()
            );
            proof
        }
        Err(e) => {
            println!("Error while getting reference_proof: {:?}", e);
            panic!("Failed to get reference_proof");
        }
    };

    println!("Getting root hash for both trees");
    // Get root hashes
    let root_merged_result = bonsai_storage.root_hash(&identifier2);
    //check if identifier contributes to root hash
    let root_reference_result = bonsai_storage3.root_hash(&identifier3);

    println!("Root hash merged_result: {:?}", root_merged_result.is_ok());
    println!(
        "Root hash reference_result: {:?}",
        root_reference_result.is_ok()
    );

    let root_merged = match root_merged_result {
        Ok(hash) => {
            println!("Root hash for merged: {:?}", hash);
            hash
        }
        Err(e) => {
            println!("Error while getting root_merged: {:?}", e);
            panic!("Failed to get root_merged");
        }
    };

    let root_reference = match root_reference_result {
        Ok(hash) => {
            println!("Root hash for reference: {:?}", hash);
            hash
        }
        Err(e) => {
            println!("Error while getting root_reference: {:?}", e);
            panic!("Failed to get root_reference");
        }
    };

    println!("Verifying proofs - should fail");
    let merged_values_result = merged_proof
        .verify_proof::<Pedersen>(root_merged, proof_keys.iter(), 24)
        .collect::<Result<Vec<_>, _>>();

    let reference_values_result = reference_proof
        .verify_proof::<Pedersen>(root_reference, proof_keys.iter(), 24)
        .collect::<Result<Vec<_>, _>>();

    // assert_ne!(
    //     merged_values_result.unwrap(),
    //     reference_values_result.unwrap(),
    //     "Values from proofs should be different"
    // );
}

#[test]
fn test_if_identifier_contributes_to_root_hash() {
    use crate::{
        databases::{create_rocks_db, RocksDB, RocksDBConfig},
        id::{BasicId, BasicIdBuilder},
        BonsaiStorage, BonsaiStorageConfig,
    };
    use starknet_types_core::{felt::Felt, hash::Pedersen};

    let db = create_rocks_db(tempfile::tempdir().unwrap().path()).unwrap();
    let identifier1 = vec![1];
    let identifier2 = vec![2];

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
    let id1 = id_builder.new_id();
    bonsai_storage.commit(id1).unwrap();

    let mut bonsai_storage2: BonsaiStorage<BasicId, RocksDB<'_, BasicId>, Pedersen> =
        BonsaiStorage::new(
            RocksDB::new(&db, RocksDBConfig::default()),
            config.clone(),
            24,
        );

    for i in 0..5 {
        let mut key = vec![0; 3];
        key[0] = i;
        let value = Felt::from(i as u64 + 100);
        bonsai_storage2
            .insert(&identifier2, &BitVec::from_vec(key), &value)
            .unwrap();
    }

    let id2 = id_builder.new_id();
    bonsai_storage2.commit(id2).unwrap();

    let root_merged_result = bonsai_storage.root_hash(&identifier1);
    let root_reference_result = bonsai_storage2.root_hash(&identifier2);

    println!(
        "Root hash for identifier 1: {:?}",
        root_merged_result.unwrap()
    );
    println!(
        "Root hash for identifier 2: {:?}",
        root_reference_result.unwrap()
    );
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

    let root_result1 = bonsai_storage.root_hash(&identifier1);
    println!("Root hash before commit: {:?}", root_result1.unwrap());

    bonsai_storage.commit(id_builder.new_id()).unwrap();
    let root_result2 = bonsai_storage.root_hash(&identifier1);

    println!("Root hash after commit: {:?}", root_result2.unwrap());
}

#[test]
fn test_merkle_proof_in_different_order() {
    use crate::{
        databases::{create_rocks_db, RocksDB, RocksDBConfig},
        id::{BasicId, BasicIdBuilder},
        BonsaiStorage, BonsaiStorageConfig,
    };
    use starknet_types_core::{felt::Felt, hash::Pedersen};

    let db = create_rocks_db(tempfile::tempdir().unwrap().path()).unwrap();
    let identifier1 = vec![1];
    let identifier2 = vec![2];

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
            .insert(&identifier1, &BitVec::from_vec(key.clone()), &value)
            .unwrap();
        println!("Inserted key ascending: {:?}, value: {:?}", key, value);
    }
    let id1 = id_builder.new_id();

    bonsai_storage.commit(id1).unwrap();

    let mut bonsai_storage2: BonsaiStorage<BasicId, RocksDB<'_, BasicId>, Pedersen> =
        BonsaiStorage::new(
            RocksDB::new(&db, RocksDBConfig::default()),
            config.clone(),
            24,
        );

    for i in (0..5).rev() {
        let mut key = vec![0; 3];
        key[0] = i;
        let value = Felt::from(i as u64 + 100);
        bonsai_storage2
            .insert(&identifier2, &BitVec::from_vec(key.clone()), &value)
            .unwrap();
        println!("Inserted key descending: {:?}, value: {:?}", key, value);
    }

    let id2 = id_builder.new_id();
    bonsai_storage2.commit(id2).unwrap();

    let ascending_root_hash = bonsai_storage.root_hash(&identifier1);
    let descending_root_hash = bonsai_storage2.root_hash(&identifier2);

    let proof_keys: Vec<BitVec> = (0..5)
        .map(|i| {
            let mut key = vec![0; 3];
            key[0] = i;
            BitVec::from_vec(key)
        })
        .collect();

    let ascending_trie_proof = bonsai_storage.get_multi_proof(&identifier1, &proof_keys);
    // println!("Ascending trie proof: {:?}", ascending_trie_proof.unwrap());
    let descending_trie_proof = bonsai_storage2.get_multi_proof(&identifier2, &proof_keys);
    // println!("Descending trie proof: {:?}", descending_trie_proof.unwrap());

    println!(
        "Root hash for identifier 1 ascending: {:?}",
        ascending_root_hash.unwrap()
    );
    println!(
        "Root hash for identifier 2 descending: {:?}",
        descending_root_hash.unwrap()
    );
}

#[test]
fn test_printing_trie() {
    use crate::{
        databases::{create_rocks_db, RocksDB, RocksDBConfig},
        id::{BasicId, BasicIdBuilder},
        BonsaiStorage, BonsaiStorageConfig,
    };
    use starknet_types_core::{felt::Felt, hash::Pedersen};

    let db = create_rocks_db(tempfile::tempdir().unwrap().path()).unwrap();
    let identifier1 = vec![1];
    let identifier2 = vec![2];

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
    let id1 = id_builder.new_id();

    bonsai_storage.commit(id1).unwrap();

    println!(
        "Trie root hash: {:?}",
        bonsai_storage.root_hash(&identifier1).unwrap()
    );

    let proof_keys: Vec<BitVec> = (0..1)
        .map(|i| {
            let mut key = vec![0; 3];
            key[0] = i;
            BitVec::from_vec(key)
        })
        .collect();

    let merged_proof_result = bonsai_storage.get_multi_proof(&identifier1, &proof_keys);
    println!("Merged proof: {:?}", merged_proof_result.unwrap());
}

#[test]
fn test_next_root() {
    use crate::{
        databases::{create_rocks_db, RocksDB, RocksDBConfig},
        id::{BasicId, BasicIdBuilder},
        BonsaiStorage, BonsaiStorageConfig,
    };
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
    let id2 = id_builder.new_id();
    bonsai_storage2.commit(id2).unwrap();

    // Get current root hash
    let current_root = bonsai_storage1.root_hash(&identifier).unwrap();
    println!("Current root hash 1: {:?}", current_root);
    let current_root2 = bonsai_storage2.root_hash(&identifier2).unwrap();
    println!("Current root hash 2: {:?}", current_root2);

    // Create a new key and value to insert
    let mut new_key = vec![0; 3];
    new_key[0] = 10;
    let new_value = Felt::from(105);
    let new_key_bv = BitVec::from_vec(new_key.clone());

    // Get the tree from bonsai_storage1
    let tree1 = bonsai_storage1
        .tries
        .trees
        .get_mut(&smallvec::smallvec![1])
        .unwrap();

    // Calculate next root using our function
    let next_root = tree1
        .next_root(&bonsai_storage1.tries.db, &new_key_bv, new_value)
        .unwrap();
    println!("Calculated next root: {:?}", next_root);

    // Actually insert the value into the second tree
    bonsai_storage2
        .insert(&identifier2, &new_key_bv, &new_value)
        .unwrap();
    bonsai_storage2.commit(id_builder.new_id()).unwrap();

    // Get the actual root hash after insertion
    let actual_root = bonsai_storage2.root_hash(&identifier2).unwrap();
    println!("Actual root after insertion: {:?}", actual_root);

    // Verify that our calculated next root matches the actual root
    assert_eq!(next_root, actual_root, "Next root calculation failed");
}
