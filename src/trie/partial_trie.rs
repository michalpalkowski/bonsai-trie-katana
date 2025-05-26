use super::iterator::PartialMerkleTreeTraverser;
use super::{
    iterator::NoopPartialVisitor,
    merkle_node::{hash_binary_node, hash_edge_node, BinaryNode, Direction, EdgeNode, Node},
    path::Path,
    proof::PartialPath,
    tree::{MerkleTree, NodeKey, RootHandle},
};
use crate::fmt;
use crate::id::BasicId;
use crate::trie::merkle_node::PartialTrieNode;
use crate::trie::merkle_node::{BinaryPartialTrieNode, EdgePartialTrieNode, ProofNodeHandle};
use crate::trie::proof::ProofVerificationError;
use crate::trie::tree::bitslice_to_bytes;
use crate::trie::tree::InsertOrRemove;
use crate::trie::TrieKey;
use crate::ByteVec;
use crate::DBError;
use crate::Id;
use crate::ProofNode;
use crate::{databases::RocksDB, BonsaiStorageError, MultiProof};
use crate::{trie::merkle_node::NodeHandle, BitSlice, BitVec};
use crate::{BonsaiDatabase, KeyValueDB};
use core::marker::PhantomData;
use hashbrown::hash_map;
use rocksdb::DB;
use starknet_types_core::{felt::Felt, hash::StarkHash};
use std::collections::HashMap;
use std::collections::HashSet;

#[derive(Debug, thiserror::Error)]
pub enum PartialTrieError {
    #[error(transparent)]
    ProofVerificationError(#[from] ProofVerificationError),
    #[error("Node not found in storage or proof")]
    NodeNotFound,
    #[error("Key length is not equal to max height")]
    KeyLength,
    #[error("Set value is zero")]
    SetValueZero,
    #[error("Invalid node handle - expected hash but got in-memory node")]
    InvalidNodeHandle,
}

impl<DBE: DBError> From<PartialTrieError> for BonsaiStorageError<DBE> {
    fn from(err: PartialTrieError) -> Self {
        BonsaiStorageError::Trie(err.to_string())
    }
}

// #[derive(Debug)]
pub struct PartialTrie<H: StarkHash> {
    pub trie: MerkleTree<H>,
    pub _hasher: PhantomData<H>,
}

impl<H: StarkHash> fmt::Debug for PartialTrie<H> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PartialTrie")
            .field("trie", &self.trie)
            .field("current_root_node_id", &self.trie.current_root_node_id)
            .field("nodes", &self.trie.nodes)
            .field("proof_nodes", &self.trie.proof_nodes)
            .field("identifier", &self.trie.identifier)
            .field("death_row", &self.trie.death_row)
            .field("cache_leaf_modified", &self.trie.cache_leaf_modified)
            .finish()
    }
}

impl<H: StarkHash + Send + Sync> PartialTrie<H> {
    pub fn new(identifier: ByteVec, max_height: u8) -> Self {
        Self {
            trie: MerkleTree::new(identifier, max_height),
            _hasher: PhantomData,
        }
    }

    /// Sets a value in the partial-trie and returns the updated root.
    /// Uses proof to fetch missing nodes.
    /// On first call, traverses the entire proof to build the tree from scratch.
    pub fn set<DB: BonsaiDatabase, ID: Id>(
        &mut self,
        db: &mut KeyValueDB<DB, ID>,
        key: &BitSlice,
        value: Felt,
        proof: MultiProof,
        original_root: Felt,
    ) -> Result<Felt, BonsaiStorageError<DB::DatabaseError>> {
        if value == Felt::ZERO {
            return Err(PartialTrieError::SetValueZero.into());
        }
        log::trace!("SET KEY: {:?}", key);
        log::trace!("SET VALUE: {:?}", value);
        log::trace!("SET ORIGINAL ROOT: {:?}", original_root);

        let path_nodes = self.get_path_for_partial_trie(&key, proof, original_root, db)?;

        log::trace!("Path nodes: {:?}", path_nodes);

        let calculated_root = self.build_from_visited_nodes(path_nodes.clone(), &key, value, db)?;

        Ok(calculated_root)
    }

    /// Builds tree from visited nodes and recursively updates hashes up the path
    fn build_from_visited_nodes<DB: BonsaiDatabase, ID: Id>(
        &mut self,
        path_nodes: Vec<(NodeKey, usize)>,
        key: &BitSlice,
        value: Felt,
        db: &mut KeyValueDB<DB, ID>,
    ) -> Result<Felt, BonsaiStorageError<DB::DatabaseError>> {
        let key_bytes = bitslice_to_bytes(key);
        match path_nodes.last() {
            Some((node_key, height)) => {
                let (current_hash, node) =
                    self.build_node_recursive(node_key, *height, key, value, &path_nodes, db)?;
                self.trie.proof_nodes[*node_key] = node;
                Ok(current_hash)
            }
            None => {
                log::trace!(
                    "Empty tree - this should never happen as we get proof from the full trie"
                );

                // Handle empty tree case
                let edge_node_hash = hash_edge_node::<H>(&Path(key.to_bitvec()), value);
                let edge_node = PartialTrieNode::Edge(EdgePartialTrieNode {
                    path: Path(key.to_bitvec()),
                    height: 0,
                    child: ProofNodeHandle::Hash(value),
                    child_handle: ProofNodeHandle::Hash(Felt::ZERO),
                });
                let node_id = self.trie.proof_nodes.insert(edge_node);
                self.trie.root_node = Some(RootHandle::Loaded(node_id));
                self.trie
                    .cache_leaf_modified
                    .insert(key_bytes, InsertOrRemove::Insert(value));

                Ok(edge_node_hash)
            }
        }
    }

    /// Works like insert in tree.rs but also updates hashes recursively up the path
    fn build_node_recursive<'a, DB: BonsaiDatabase, ID: Id>(
        &mut self,
        node_key: &NodeKey,
        height: usize,
        key: &BitSlice,
        value: Felt,
        path_nodes: &[(NodeKey, usize)],
        db: &mut KeyValueDB<DB, ID>,
    ) -> Result<(Felt, PartialTrieNode), BonsaiStorageError<DB::DatabaseError>> {
        let mut node = self
            .trie
            .get_proof_node_mut::<DB>(*node_key)
            .map_err(|_| PartialTrieError::NodeNotFound)?
            .clone();

        match &mut node {
            PartialTrieNode::Edge(edge) => {
                log::trace!("EDGE: {:?}", edge);
                let common = edge.common_path(key);
                let branch_height = edge.height as usize + common.len();

                if branch_height == key.len() {
                    let key_bytes = bitslice_to_bytes(key);
                    edge.child = ProofNodeHandle::Hash(value);
                    self.trie
                        .cache_leaf_modified
                        .insert(key_bytes, InsertOrRemove::Insert(value));
                    let final_hash = self.hash_up_merkle_path(key, value, path_nodes, false)?;
                    return Ok((final_hash, node));
                }

                let child_height = branch_height + 1;
                // Path from binary node to new leaf
                let new_path = key[child_height..].to_bitvec();
                // Path from binary node to existing child
                let old_path = edge.path[common.len() + 1..].to_bitvec();

                let (new_hash, new_id) = if new_path.is_empty() {
                    (
                        ProofNodeHandle::Hash(value),
                        ProofNodeHandle::Hash(Felt::ZERO),
                    )
                } else {
                    let edge_hash = hash_edge_node::<H>(&Path(new_path.clone()), value);
                    let edge_node = PartialTrieNode::Edge(EdgePartialTrieNode {
                        path: Path(new_path),
                        height: child_height as u64,
                        child: ProofNodeHandle::Hash(value),
                        child_handle: ProofNodeHandle::Hash(Felt::ZERO),
                    });
                    let edge_id = self.trie.proof_nodes.insert(edge_node);
                    (
                        ProofNodeHandle::Hash(edge_hash),
                        ProofNodeHandle::InMemory(edge_id),
                    )
                };

                let (old_hash, old_id) = if old_path.is_empty() {
                    (edge.child, edge.child_handle)
                } else {
                    let child_hash = edge
                        .child
                        .as_hash()
                        .ok_or(PartialTrieError::InvalidNodeHandle)?;
                    let edge_hash = hash_edge_node::<H>(&Path(old_path.clone()), child_hash);
                    let edge_node = PartialTrieNode::Edge(EdgePartialTrieNode {
                        path: Path(old_path),
                        height: child_height as u64,
                        child: edge.child,
                        child_handle: edge.child_handle,
                    });

                    let edge_id = self.trie.proof_nodes.insert(edge_node);

                    (
                        ProofNodeHandle::Hash(edge_hash),
                        ProofNodeHandle::InMemory(edge_id),
                    )
                };

                let new_direction = Direction::from(key[branch_height]);
                let ((left, left_child), (right, right_child)) = match new_direction {
                    Direction::Left => ((new_hash, new_id), (old_hash, old_id)),
                    Direction::Right => ((old_hash, old_id), (new_hash, new_id)),
                };

                let left_hash = left.as_hash().ok_or(PartialTrieError::InvalidNodeHandle)?;
                let right_hash = right.as_hash().ok_or(PartialTrieError::InvalidNodeHandle)?;
                let branch_hash = hash_binary_node::<H>(left_hash, right_hash);

                let branch = PartialTrieNode::Binary(BinaryPartialTrieNode {
                    height: branch_height as u64,
                    left: left,
                    right: right,
                    left_handle: left_child,
                    right_handle: right_child,
                });

                let (current_hash, new_node) = if common.is_empty() {
                    (branch_hash, branch)
                } else {
                    let edge_node_hash =
                        hash_edge_node::<H>(&Path(common.to_bitvec()), branch_hash);
                    let branch_node_key = self.trie.proof_nodes.insert(branch);

                    let new_node = PartialTrieNode::Edge(EdgePartialTrieNode {
                        path: Path(common.to_bitvec()),
                        height: edge.height,
                        child: ProofNodeHandle::Hash(branch_hash),
                        child_handle: ProofNodeHandle::InMemory(branch_node_key),
                    });
                    (edge_node_hash, new_node)
                };

                node = new_node;

                let final_hash = self.hash_up_merkle_path(key, current_hash, path_nodes, true)?;

                let key_bytes = bitslice_to_bytes(&key[..height as usize]);
                log::trace!("Adding to death row: {:?}", key_bytes);
                self.trie.death_row.insert(TrieKey::Trie(key_bytes));
                Ok((final_hash, node))
            }
            PartialTrieNode::Binary(binary) => {
                log::trace!("BINARY: {:?}", binary);
                let child_height = binary.height + 1;
                let direction = Direction::from(key[binary.height as usize]);

                if child_height as usize == key.len() {
                    let current_hash = match direction {
                        Direction::Left => {
                            let right_hash = binary
                                .right
                                .as_hash()
                                .ok_or(PartialTrieError::InvalidNodeHandle)?;
                            let binary_node = hash_binary_node::<H>(value, right_hash);
                            binary.left = ProofNodeHandle::Hash(value);

                            binary_node
                        }
                        Direction::Right => {
                            let left_hash = binary
                                .left
                                .as_hash()
                                .ok_or(PartialTrieError::InvalidNodeHandle)?;
                            let binary_node = hash_binary_node::<H>(left_hash, value);
                            binary.right = ProofNodeHandle::Hash(value);

                            binary_node
                        }
                    };
                    let key_bytes = bitslice_to_bytes(key);
                    self.trie
                        .cache_leaf_modified
                        .insert(key_bytes, InsertOrRemove::Insert(value));

                    let final_hash =
                        self.hash_up_merkle_path(key, current_hash, path_nodes, true)?;
                    Ok((final_hash, node))
                } else {
                    log::trace!("Binary node not at path end - should fetch full trie");
                    Err(PartialTrieError::NodeNotFound.into())
                }
            }
        }
    }

    /// This function hashes up the path
    fn hash_up_merkle_path(
        &mut self,
        key: &BitSlice,
        current_hash: Felt,
        path_nodes: &[(NodeKey, usize)],
        skip_last: bool,
    ) -> Result<Felt, PartialTrieError> {
        let mut nodes = path_nodes.iter().rev().skip(if skip_last { 1 } else { 0 });

        self.hash_up_recursive(key, current_hash, &mut nodes)
    }

    /// Recursively hashes up the path
    fn hash_up_recursive<'a, I>(
        &mut self,
        key: &BitSlice,
        current_hash: Felt,
        nodes: &mut I,
    ) -> Result<Felt, PartialTrieError>
    where
        I: Iterator<Item = &'a (NodeKey, usize)>,
    {
        if let Some((node_key, height)) = nodes.next() {
            let node = self
                .trie
                .proof_nodes
                .get(*node_key)
                .ok_or(PartialTrieError::NodeNotFound)?
                .clone();
            match node {
                PartialTrieNode::Binary(binary) => {
                    let direction = Direction::from(key[*height as usize]);
                    let new_hash = match direction {
                        Direction::Left => {
                            let right_hash = binary
                                .right
                                .as_hash()
                                .ok_or(PartialTrieError::InvalidNodeHandle)?;
                            let binary_node = hash_binary_node::<H>(current_hash, right_hash);
                            self.trie.proof_nodes[*node_key] =
                                PartialTrieNode::Binary(BinaryPartialTrieNode {
                                    left: ProofNodeHandle::Hash(current_hash),
                                    ..binary
                                });
                            binary_node
                        }
                        Direction::Right => {
                            let left_hash = binary
                                .left
                                .as_hash()
                                .ok_or(PartialTrieError::InvalidNodeHandle)?;
                            let binary_node = hash_binary_node::<H>(left_hash, current_hash);
                            self.trie.proof_nodes[*node_key] =
                                PartialTrieNode::Binary(BinaryPartialTrieNode {
                                    right: ProofNodeHandle::Hash(current_hash),
                                    ..binary
                                });
                            binary_node
                        }
                    };
                    self.hash_up_recursive(key, new_hash, nodes)
                }
                PartialTrieNode::Edge(edge) => {
                    let edge_node = hash_edge_node::<H>(&edge.path, current_hash);
                    self.trie.proof_nodes[*node_key] = PartialTrieNode::Edge(EdgePartialTrieNode {
                        path: edge.path.clone(),
                        child: ProofNodeHandle::Hash(current_hash),
                        ..edge
                    });
                    self.hash_up_recursive(key, edge_node, nodes)
                }
            }
        } else {
            Ok(current_hash)
        }
    }

    /// Traverses the current partial tree and collects existing elements.
    /// If an element is missing, selects it from the proof.
    /// If the tree is empty, completes it from the proof.
    pub fn get_path_for_partial_trie<DB: BonsaiDatabase, ID: Id>(
        &mut self,
        key: &BitSlice,
        proof: MultiProof,
        original_root: Felt,
        db: &KeyValueDB<DB, ID>,
    ) -> Result<Vec<(NodeKey, usize)>, BonsaiStorageError<DB::DatabaseError>> {
        let proof_keys = vec![key];
        let max_height = self.trie.max_height;
        let mut iter = self.trie.iter_partial_trie(db, proof);
        let mut visitor = NoopPartialVisitor::<H>(PhantomData);

        for key in proof_keys {
            let key = key.as_ref();
            if key.len() != max_height as usize {
                return Err(PartialTrieError::KeyLength.into());
            }
            iter.traverse_to::<NoopPartialVisitor<H>>(&mut visitor, key, original_root)?;
        }
        let path_nodes = iter.current_partial_nodes_heights;

        Ok(path_nodes)
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        databases::{create_rocks_db, RocksDB, RocksDBConfig},
        id::{BasicId, BasicIdBuilder},
        BonsaiStorage, BonsaiStorageConfig, PartialMerkleTrees,
    };
    use bitvec::{bits, prelude::Msb0};
    use proptest::collection::vec;
    use proptest::num::u8;
    use proptest::prelude::*;
    use starknet_types_core::hash::Pedersen;

    fn arb_key(max_height: u8) -> impl Strategy<Value = BitVec> {
        prop::collection::vec(any::<bool>(), max_height as usize)
            .prop_map(|bits| bits.into_iter().collect())
    }

    fn arb_key_value(max_height: u8) -> impl Strategy<Value = (BitVec, Felt)> {
        (
            prop::collection::vec(any::<bool>(), max_height as usize),
            (1..=254u8),
        )
            .prop_map(move |(bits, v)| {
                let mut key = BitVec::with_capacity(max_height as usize);
                key.extend(bits);
                debug_assert_eq!(
                    key.len(),
                    max_height as usize,
                    "Key length must match max_height"
                );
                let value = Felt::from(v as u64 + 1);
                (key, value)
            })
    }

    fn arb_value() -> impl Strategy<Value = Felt> {
        u8::ANY.prop_map(|v| Felt::from(v as u64 + 100))
    }

    fn arb_power_of_two_keys(max_height: u8) -> impl Strategy<Value = Vec<(BitVec, Felt)>> {
        (0..4).prop_flat_map(move |power| {
            let num_keys = 1 << power;
            prop::collection::vec(arb_key_value(max_height), num_keys as usize)
        })
    }

    //TODO: DECIDE WHAT TO DO WITH THIS
    fn select_random_key_value_from_initial_keys(
        initial_keys_values: Vec<(BitVec, Felt)>,
    ) -> (BitVec, Felt, Vec<(BitVec, Felt)>) {
        assert!(!initial_keys_values.is_empty(), "empty key/value set");
        let random_index = rand::random::<usize>() % initial_keys_values.len();
        let (removed_key, removed_value) = initial_keys_values[random_index].clone();

        let remaining_keys_values: Vec<(BitVec, Felt)> = initial_keys_values
            .into_iter()
            .enumerate()
            .filter(|(i, _)| *i != random_index)
            .map(|(_, kv)| kv)
            .collect();

        (removed_key, removed_value, remaining_keys_values)
    }

    #[test]
    fn test_set_root_multiple_calls_single_test_height_8() {
        let base_path = tempfile::tempdir().unwrap().path().to_path_buf();
        let base_db = create_rocks_db(&base_path).unwrap();

        let reference_path = tempfile::tempdir().unwrap().path().to_path_buf();
        let reference_db = create_rocks_db(&reference_path).unwrap();

        let fork_path = tempfile::tempdir().unwrap().path().to_path_buf();
        let fork_db = create_rocks_db(&fork_path).unwrap();

        let tree_to_compare_path = tempfile::tempdir().unwrap().path().to_path_buf();
        let tree_to_compare_db = create_rocks_db(&tree_to_compare_path).unwrap();

        let identifier = vec![1];
        let identifier2 = vec![2];
        let identifier3 = vec![3];
        let identifier4 = vec![4];

        let config = BonsaiStorageConfig::default();
        let mut base_tree: BonsaiStorage<BasicId, RocksDB<'_, BasicId>, Pedersen> =
            BonsaiStorage::new(
                RocksDB::new(&base_db, RocksDBConfig::default()),
                config.clone(),
                8,
            );
        let mut tree_to_compare: BonsaiStorage<BasicId, RocksDB<'_, BasicId>, Pedersen> =
            BonsaiStorage::new(
                RocksDB::new(&tree_to_compare_db, RocksDBConfig::default()),
                config.clone(),
                8,
            );
        let mut reference_tree: BonsaiStorage<BasicId, RocksDB<'_, BasicId>, Pedersen> =
            BonsaiStorage::new(
                RocksDB::new(&reference_db, RocksDBConfig::default()),
                config.clone(),
                8,
            );
        let mut fork_tree: BonsaiStorage<BasicId, RocksDB<'_, BasicId>, Pedersen> =
            BonsaiStorage::new(
                RocksDB::new(&fork_db, RocksDBConfig::default()),
                config.clone(),
                8,
            );

        let mut id_builder = BasicIdBuilder::new();

        let one = bits![u8,   Msb0; 1,0,0,0,0,0,0,0];
        let two = bits![u8,   Msb0; 0,1,0,0,0,0,0,0];
        let three = bits![u8, Msb0; 1,1,0,0,0,0,0,0];
        let four = bits![u8,  Msb0; 0,0,1,0,0,0,0,0];
        let five = bits![u8,  Msb0; 1,0,1,0,0,0,0,0];
        let six = bits![u8,   Msb0; 0,1,1,0,0,0,0,0];
        let seven = bits![u8, Msb0; 1,1,1,0,0,0,0,0];
        let eight = bits![u8, Msb0; 0,0,0,1,0,0,0,0];
        let nine = bits![u8,  Msb0; 1,0,0,1,0,0,0,0];
        let ten = bits![u8,   Msb0; 0,0,0,0,1,0,1,0];
        let eleven = bits![u8,Msb0; 0,0,0,0,1,0,1,1];
        let twelve = bits![u8,Msb0; 0,0,0,0,1,1,0,0];

        let keys = vec![
            one, two, three, four, five, six, seven, eight, nine, ten, eleven, twelve,
        ];
        let values = vec![
            Felt::from(1),
            Felt::from(2),
            Felt::from(3),
            Felt::from(4),
            Felt::from(5),
            Felt::from(6),
            Felt::from(7),
            Felt::from(8),
            Felt::from(9),
            Felt::from(10),
            Felt::from(11),
            Felt::from(12),
        ];

        for (key, value) in keys.iter().zip(values.iter()).take(3) {
            println!("Inserting key: {:?}", key);
            println!("Inserting value: {:?}", value);
            base_tree.insert(&identifier, key, value).unwrap();
            reference_tree.insert(&identifier3, key, value).unwrap(); // thats a referencje tree
                                                                      // println!("bonsai trie: {:?}", bonsai_storage1.tries.trees.entry(smallvec::smallvec![1]).unwrap().proof_nodes);
        }

        base_tree.commit(id_builder.new_id()).unwrap();
        let original_root = base_tree.root_hash(&identifier).unwrap();
        println!("Original root: {:?}", original_root);

        let mut partial_trie = PartialTrie::<Pedersen>::new(identifier4.clone().into(), 8);
        let mut calculated_roots: Vec<Felt> = Vec::new();
        let mut i = 0;
        let mut current_root = original_root;

        let tree1 = base_tree
            .tries
            .trees
            .entry(smallvec::smallvec![1])
            .or_insert_with(|| MerkleTree::new(identifier.clone().into(), 8));

        let proof_key_one = vec![one];
        let proof_for_one = tree1
            .get_multi_proof(&base_tree.tries.db, proof_key_one.iter())
            .unwrap();
        println!("Proof for one: {:?}", proof_for_one);

        for (key, value) in keys.iter().zip(values.iter()).skip(3) {
            i += 1;
            println!("ITERATION: {:?}", i);

            let proof_keys = vec![key];

            let proof = tree1
                .get_multi_proof(&base_tree.tries.db, proof_keys.iter())
                .unwrap();

            println!("---------PROOF-------");
            println!("{:?}\n", proof);

            // println!("\ntree: {:?}\n", bonsai_storage1.tries.trees.entry(smallvec::smallvec![1]));
            reference_tree.insert(&identifier3, key, value).unwrap();
            println!(
                "\nTree NODES: {:?}\n",
                reference_tree
                    .tries
                    .trees
                    .get(&smallvec::smallvec![3])
                    .unwrap()
                    .nodes
                    .iter()
                    .map(|(k, v)| (k, v))
                    .collect::<HashMap<_, _>>()
            );
            println!(
                "\nPartialTree NODES before adding new key-value pair: {:?}\n",
                partial_trie
                    .trie
                    .proof_nodes
                    .iter()
                    .map(|(k, v)| (k, v))
                    .collect::<HashMap<_, _>>()
            );
            reference_tree.commit(id_builder.new_id()).unwrap();

            let calculated_root = partial_trie
                .set(&mut fork_tree.tries.db, key, *value, proof, original_root)
                .unwrap();
            println!("Calculated root: {:?}\n", calculated_root);

            println!("Partial TRIE: {:?}\n", partial_trie.trie.proof_nodes);
            println!(
                "\nPartialTree NODES after adding new key-value pair: {:?}\n",
                partial_trie
                    .trie
                    .proof_nodes
                    .iter()
                    .map(|(k, v)| (k, v))
                    .collect::<HashMap<_, _>>()
            );

            calculated_roots.push(calculated_root);
            current_root = calculated_root;
        }

        for (key, value) in keys.iter().zip(values.iter()) {
            tree_to_compare.insert(&identifier2, key, value).unwrap();
        }

        //we update the full trie with new values which we inserted with build_from_visited_nodes() method
        // just to be sure that we have the correct root
        tree_to_compare.commit(id_builder.new_id()).unwrap();
        let proof_keys = vec![keys.last().unwrap()];
        let proof = tree1
            .get_multi_proof(&tree_to_compare.tries.db, proof_keys.iter())
            .unwrap();

        let actual_root = tree_to_compare.root_hash(&identifier2).unwrap();
        assert_eq!(current_root, actual_root, "Next root calculation failed");

        println!(
            "Partial TRIE before updating root: {:?}\n",
            partial_trie.trie.proof_nodes
        );
        println!(
            "\nPartialTree NODES before updating root: {:?}\n",
            partial_trie
                .trie
                .proof_nodes
                .iter()
                .map(|(k, v)| (k, v))
                .collect::<HashMap<_, _>>()
        );

        let calculated_updated_root = partial_trie
            .set(
                &mut fork_tree.tries.db,
                one,
                Felt::from(13),
                proof_for_one,
                original_root,
            )
            .unwrap();
        println!("Calculated root: {:?}\n", calculated_updated_root);

        tree_to_compare
            .insert(&identifier2, one, &Felt::from(13))
            .unwrap();
        tree_to_compare.commit(id_builder.new_id()).unwrap();

        let actual_updated_root = tree_to_compare.root_hash(&identifier2).unwrap();
        assert_eq!(
            calculated_updated_root, actual_updated_root,
            "UPDATING ROOT FAILED"
        );
    }

    proptest! {
        #![proptest_config(ProptestConfig::default())]
        #[test]
        fn test_set_root_multiple_calls_height_2(
            initial_keys_values in arb_power_of_two_keys(2),
            new_keys_values in vec(arb_key_value(2), 1..3),
        ) {
            println!("initial_keys_values: {:?}", initial_keys_values);
            println!("new_keys_values: {:?}", new_keys_values);
            test_set_root_multiple_calls(2, initial_keys_values, new_keys_values);
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::default())]
        #[test]
        fn test_set_root_multiple_calls_height_4(
            initial_keys_values in arb_power_of_two_keys(4),
            new_keys_values in vec(arb_key_value(4), 1..5),
        ) {
            println!("initial_keys_values: {:?}", initial_keys_values);
            println!("new_keys_values: {:?}", new_keys_values);
            test_set_root_multiple_calls(4, initial_keys_values, new_keys_values);
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::default())]
        #[test]
        fn test_set_root_multiple_calls_height_8(
            initial_keys_values in arb_power_of_two_keys(8),
            new_keys_values in vec(arb_key_value(8), 1..20),
        ) {
            test_set_root_multiple_calls(8, initial_keys_values, new_keys_values);
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::default())]
        #[test]
        fn test_set_root_multiple_calls_height_24(
            initial_keys_values in arb_power_of_two_keys(24),
            new_keys_values in vec(arb_key_value(24), 1..5),
        ) {
            test_set_root_multiple_calls(24, initial_keys_values, new_keys_values);
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::default())]
        #[test]
        fn test_set_root_multiple_calls_height_251(
            initial_keys_values in arb_power_of_two_keys(251),
            new_keys_values in vec(arb_key_value(251), 1..5),
        ) {
            test_set_root_multiple_calls(251, initial_keys_values, new_keys_values);
        }
    }

    fn test_set_root_multiple_calls(
        height: u8,
        initial_keys_values: Vec<(BitVec, Felt)>,
        new_keys_values: Vec<(BitVec, Felt)>,
    ) {
        let base_db = create_rocks_db(tempfile::tempdir().unwrap().path()).unwrap();
        let reference_db = create_rocks_db(tempfile::tempdir().unwrap().path()).unwrap();
        let fork_db = create_rocks_db(tempfile::tempdir().unwrap().path()).unwrap();

        let base_identifier = vec![1];
        let reference_identifier = vec![2];
        let fork_identifier = vec![3];

        let config = BonsaiStorageConfig::default();
        let mut base_bonsai_storage: BonsaiStorage<BasicId, RocksDB<'_, BasicId>, Pedersen> =
            BonsaiStorage::new(
                RocksDB::new(&base_db, RocksDBConfig::default()),
                config.clone(),
                height,
            );
        let mut reference_bonsai_storage: BonsaiStorage<BasicId, RocksDB<'_, BasicId>, Pedersen> =
            BonsaiStorage::new(
                RocksDB::new(&reference_db, RocksDBConfig::default()),
                config.clone(),
                height,
            );
        let mut forked_bonsai_storage: BonsaiStorage<BasicId, RocksDB<'_, BasicId>, Pedersen> =
            BonsaiStorage::new(
                RocksDB::new(&fork_db, RocksDBConfig::default()),
                config.clone(),
                height,
            );

        let mut id_builder = BasicIdBuilder::new();

        for (key, value) in initial_keys_values.iter() {
            base_bonsai_storage
                .insert(&base_identifier, key, value)
                .unwrap();
            reference_bonsai_storage
                .insert(&reference_identifier, key, value)
                .unwrap();
            base_bonsai_storage.commit(id_builder.new_id()).unwrap();
            reference_bonsai_storage
                .commit(id_builder.new_id())
                .unwrap();
        }

        let original_root = base_bonsai_storage.root_hash(&base_identifier).unwrap();

        let mut partial_trie = PartialTrie::<Pedersen>::new(fork_identifier.clone().into(), height);

        let mut calculated_roots = Vec::new();

        let tree1 = base_bonsai_storage
            .tries
            .trees
            .entry(smallvec::smallvec![1])
            .or_insert_with(|| MerkleTree::new(base_identifier.clone().into(), height));

        let mut i = 0;
        for (key, value) in new_keys_values.iter() {
            i += 1;
            let proof_keys = vec![key];
            let proof = tree1
                .get_multi_proof(&base_bonsai_storage.tries.db, proof_keys.iter())
                .unwrap();

            println!("\nITERATION: {:?}\n", i);
            println!("\nProof: {:?}\n", proof);

            let calculated_root = partial_trie
                .set(
                    &mut forked_bonsai_storage.tries.db,
                    key,
                    *value,
                    proof,
                    original_root,
                )
                .unwrap();

            println!(
                "\nPartialTree NODES after adding new key-value pair: {:?}\n",
                partial_trie
                    .trie
                    .proof_nodes
                    .iter()
                    .map(|(k, v)| (k, v))
                    .collect::<HashMap<_, _>>()
            );

            calculated_roots.push(calculated_root);
        }

        for ((key, value), expected_root) in new_keys_values.iter().zip(calculated_roots) {
            reference_bonsai_storage
                .insert(&reference_identifier, key, value)
                .unwrap();
            reference_bonsai_storage
                .commit(id_builder.new_id())
                .unwrap();

            let actual_root = reference_bonsai_storage
                .root_hash(&reference_identifier)
                .unwrap();
            println!("Expected root: {:?}", expected_root);
            println!("Actual root: {:?}", actual_root);
            assert_eq!(expected_root, actual_root);
        }
    }
    #[test]
    fn test_bonsai_partial_trie() {
        let base_path = tempfile::tempdir().unwrap().path().to_path_buf();
        let base_db = create_rocks_db(&base_path).unwrap();

        let reference_path = tempfile::tempdir().unwrap().path().to_path_buf();
        let reference_db = create_rocks_db(&reference_path).unwrap();

        let fork_path = tempfile::tempdir().unwrap().path().to_path_buf();
        let fork_db = create_rocks_db(&fork_path).unwrap();

        let tree_to_compare_path = tempfile::tempdir().unwrap().path().to_path_buf();
        let tree_to_compare_db = create_rocks_db(&tree_to_compare_path).unwrap();

        let identifier = vec![1];
        let identifier2 = vec![2];
        let identifier3 = vec![3];
        let identifier4 = vec![4];

        let config = BonsaiStorageConfig::default();
        let mut base_tree: BonsaiStorage<BasicId, RocksDB<'_, BasicId>, Pedersen> =
            BonsaiStorage::new(
                RocksDB::new(&base_db, RocksDBConfig::default()),
                config.clone(),
                8,
            );
        let mut tree_to_compare: BonsaiStorage<BasicId, RocksDB<'_, BasicId>, Pedersen> =
            BonsaiStorage::new(
                RocksDB::new(&tree_to_compare_db, RocksDBConfig::default()),
                config.clone(),
                8,
            );
        let mut reference_tree: BonsaiStorage<BasicId, RocksDB<'_, BasicId>, Pedersen> =
            BonsaiStorage::new(
                RocksDB::new(&reference_db, RocksDBConfig::default()),
                config.clone(),
                8,
            );
        let mut fork_tree: BonsaiStorage<
            BasicId,
            RocksDB<'_, BasicId>,
            Pedersen,
            PartialMerkleTrees<Pedersen, RocksDB<'_, BasicId>, BasicId>,
        > = BonsaiStorage::new_partial(
            RocksDB::new(&fork_db, RocksDBConfig::default()),
            config.clone(),
            8,
        );

        let mut id_builder = BasicIdBuilder::new();

        let one = bits![u8,   Msb0; 1,0,0,0,0,0,0,0];
        let two = bits![u8,   Msb0; 0,1,0,0,0,0,0,0];
        let three = bits![u8, Msb0; 1,1,0,0,0,0,0,0];
        let four = bits![u8,  Msb0; 0,0,1,0,0,0,0,0];
        let five = bits![u8,  Msb0; 1,0,1,0,0,0,0,0];
        let six = bits![u8,   Msb0; 0,1,1,0,0,0,0,0];
        let seven = bits![u8, Msb0; 1,1,1,0,0,0,0,0];
        let eight = bits![u8, Msb0; 0,0,0,1,0,0,0,0];
        let nine = bits![u8,  Msb0; 1,0,0,1,0,0,0,0];
        let ten = bits![u8,   Msb0; 0,0,0,0,1,0,1,0];
        let eleven = bits![u8,Msb0; 0,0,0,0,1,0,1,1];
        let twelve = bits![u8,Msb0; 0,0,0,0,1,1,0,0];

        let keys = vec![
            one, two, three, four, five, six, seven, eight, nine, ten, eleven, twelve,
        ];
        let values = vec![
            Felt::from(1),
            Felt::from(2),
            Felt::from(3),
            Felt::from(4),
            Felt::from(5),
            Felt::from(6),
            Felt::from(7),
            Felt::from(8),
            Felt::from(9),
            Felt::from(10),
            Felt::from(11),
            Felt::from(12),
        ];

        for (key, value) in keys.iter().zip(values.iter()).take(3) {
            println!("Inserting key: {:?}", key);
            println!("Inserting value: {:?}", value);
            base_tree.insert(&identifier, key, value).unwrap();
            reference_tree.insert(&identifier3, key, value).unwrap(); // thats a referencje tree
                                                                      // println!("bonsai trie: {:?}", bonsai_storage1.tries.trees.entry(smallvec::smallvec![1]).unwrap().proof_nodes);
        }

        base_tree.commit(id_builder.new_id()).unwrap();
        let original_root = base_tree.root_hash(&identifier).unwrap();
        println!("Original root: {:?}", original_root);

        let mut partial_trie = PartialTrie::<Pedersen>::new(identifier4.clone().into(), 8);
        let mut calculated_roots: Vec<Felt> = Vec::new();
        let mut i = 0;
        let mut current_root = original_root;

        let tree1 = base_tree
            .tries
            .trees
            .entry(smallvec::smallvec![1])
            .or_insert_with(|| MerkleTree::new(identifier.clone().into(), 8));

        let proof_key_one = vec![one];
        let proof_for_one = tree1
            .get_multi_proof(&base_tree.tries.db, proof_key_one.iter())
            .unwrap();
        println!("Proof for one: {:?}", proof_for_one);

        for (key, value) in keys.iter().zip(values.iter()).skip(3) {
            i += 1;
            println!("ITERATION: {:?}", i);

            let proof_keys = vec![key];

            let proof = tree1
                .get_multi_proof(&base_tree.tries.db, proof_keys.iter())
                .unwrap();

            println!("---------PROOF-------");
            println!("{:?}\n", proof);

            // println!("\ntree: {:?}\n", bonsai_storage1.tries.trees.entry(smallvec::smallvec![1]));
            reference_tree.insert(&identifier3, key, value).unwrap();
            println!(
                "\nTree NODES: {:?}\n",
                reference_tree
                    .tries
                    .trees
                    .get(&smallvec::smallvec![3])
                    .unwrap()
                    .nodes
                    .iter()
                    .map(|(k, v)| (k, v))
                    .collect::<HashMap<_, _>>()
            );
            println!(
                "\nPartialTree NODES before adding new key-value pair: {:?}\n",
                partial_trie
                    .trie
                    .proof_nodes
                    .iter()
                    .map(|(k, v)| (k, v))
                    .collect::<HashMap<_, _>>()
            );
            reference_tree.commit(id_builder.new_id()).unwrap();

            // let calculated_root = partial_trie
            //     .set(&mut fork_tree.tries.db, key, *value, proof, original_root)
            //     .unwrap();
            // println!("Calculated root: {:?}\n", calculated_root);

            let calculated_root = fork_tree
                .insert_with_proof(&identifier4, key, value, proof, original_root)
                .unwrap();

            println!("Partial TRIE: {:?}\n", partial_trie.trie.proof_nodes);
            println!(
                "\nPartialTree NODES after adding new key-value pair: {:?}\n",
                partial_trie
                    .trie
                    .proof_nodes
                    .iter()
                    .map(|(k, v)| (k, v))
                    .collect::<HashMap<_, _>>()
            );

            calculated_roots.push(calculated_root);
            current_root = calculated_root;
        }

        for (key, value) in keys.iter().zip(values.iter()) {
            tree_to_compare.insert(&identifier2, key, value).unwrap();
        }

        //we update the full trie with new values which we inserted with build_from_visited_nodes() method
        // just to be sure that we have the correct root
        tree_to_compare.commit(id_builder.new_id()).unwrap();
        let proof_keys = vec![keys.last().unwrap()];
        let proof = tree1
            .get_multi_proof(&tree_to_compare.tries.db, proof_keys.iter())
            .unwrap();

        let actual_root = tree_to_compare.root_hash(&identifier2).unwrap();
        assert_eq!(current_root, actual_root, "Next root calculation failed");

        println!(
            "Partial TRIE before updating root: {:?}\n",
            partial_trie.trie.proof_nodes
        );
        println!(
            "\nPartialTree NODES before updating root: {:?}\n",
            partial_trie
                .trie
                .proof_nodes
                .iter()
                .map(|(k, v)| (k, v))
                .collect::<HashMap<_, _>>()
        );

        let calculated_updated_root = fork_tree
            .insert_with_proof(
                &identifier4,
                one,
                &Felt::from(13),
                proof_for_one,
                original_root,
            )
            .unwrap();
        println!("Calculated root: {:?}\n", calculated_updated_root);

        tree_to_compare
            .insert(&identifier2, one, &Felt::from(13))
            .unwrap();
        tree_to_compare.commit(id_builder.new_id()).unwrap();

        let actual_updated_root = tree_to_compare.root_hash(&identifier2).unwrap();
        assert_eq!(
            calculated_updated_root, actual_updated_root,
            "UPDATING ROOT FAILED"
        );
    }
}
