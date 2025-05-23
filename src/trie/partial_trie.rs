use super::{
    iterator::NoopPartialVisitor,
    merkle_node::{hash_binary_node, hash_edge_node, BinaryNode, Direction, EdgeNode, Node},
    path::Path,
    proof::PartialPath,
    tree::{MerkleTree, NodeKey, ProofNodeChildren, RootHandle},
};
use crate::id::BasicId;
use crate::trie::merkle_node::{BinaryPartialTrieNode, EdgePartialTrieNode, ProofNodeHandle};
use crate::trie::proof::common_path;
use crate::trie::proof::ProofVerificationError;
use crate::trie::tree::bitslice_to_bytes;
use crate::trie::tree::InsertOrRemove;
use crate::trie::TrieKey;
use crate::ByteVec;
use crate::ProofNode;
use crate::{databases::RocksDB, BonsaiStorageError, MultiProof};
use crate::{trie::merkle_node::NodeHandle, BitSlice, BitVec};
use crate::{BonsaiDatabase, KeyValueDB};
use core::marker::PhantomData;
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
}

#[derive(Debug)]
struct PartialTrie<H: StarkHash> {
    trie: MerkleTree<H>,
    max_height: u8,
    original_root: Felt,
    _hasher: PhantomData<H>,
}

impl<H: StarkHash + Send + Sync> PartialTrie<H> {
    fn new(identifier: ByteVec, max_height: u8, original_root: Felt) -> Self {
        Self {
            trie: MerkleTree::new(identifier, max_height),
            max_height,
            original_root,
            _hasher: PhantomData,
        }
    }

    /// This function sets a value in the partial-trie and returns the updated root
    /// It takes nodes which are not in the trie from proof
    /// On first call it will traverse whole proof and build tree from scratch
    fn set(
        &mut self,
        db: &mut KeyValueDB<RocksDB<BasicId>, BasicId>,
        key: &BitSlice,
        value: Felt,
        proof: MultiProof,
        original_root: Felt,
    ) -> Result<Felt, PartialTrieError> {
        //Traverse tree insert nodes and return path
        let path_nodes = self
            .get_partial_path_from_existing_trie(&key, proof, original_root, db)
            .unwrap();

        println!("PATH NODES: {:?}\n", path_nodes);

        //Build tree from visited nodes
        let calculated_root = self
            .build_from_visited_nodes(path_nodes.clone(), &key, value, db)
            .unwrap();

        Ok(calculated_root)
    }

    /// This function creates a binary node and inserts it into the trie
    fn create_binary_node(
        &mut self,
        branch_height: usize,
        left: Felt,
        right: Felt,
        left_child_key: Option<NodeKey>,
        right_child_key: Option<NodeKey>,
    ) -> Result<NodeKey, PartialTrieError> {
        self.trie
            .insert_binary_node(branch_height, left, right, left_child_key, right_child_key)
    }

    fn update_cache(&mut self, key: &BitSlice, value: Felt) {
        let key_bytes = bitslice_to_bytes(key);
        self.trie
            .cache_leaf_modified
            .insert(key_bytes, InsertOrRemove::Insert(value));
    }

    /// This function builds tree from visited nodes and recursively updates hashes up the path
    fn build_from_visited_nodes(
        &mut self,
        mut path_nodes: Vec<(NodeKey, usize)>,
        key: &BitSlice,
        value: Felt,
        db: &mut KeyValueDB<RocksDB<BasicId>, BasicId>,
    ) -> Result<Felt, PartialTrieError> {
        println!("---------VISITED NODES-----------");
        println!("{:?}\n", path_nodes);

        let key_bytes = bitslice_to_bytes(key);

        match path_nodes.last() {
            Some((node_key, height)) => {
                let (current_hash, node, children) =
                    self.build_node_recursive(node_key, *height, key, value, &path_nodes, db)?;
                self.trie.proof_nodes[*node_key] = (node, children);
                Ok(current_hash)
            }
            None => {
                println!("WE HAVE EMPTY TREE, THIS SHOULD NEVER HAPPEN AS WE GET PROOF FROM THE FULL TRIE");

                // Handle empty tree case
                let edge_node = hash_edge_node::<H>(&Path(key.to_bitvec()), value);
                let node_id =
                    self.trie
                        .insert_edge_node(0, &Path(key.to_bitvec()), value, edge_node, key)?;
                self.trie.root_node = Some(RootHandle::Loaded(node_id));
                self.trie
                    .cache_leaf_modified
                    .insert(key_bytes, InsertOrRemove::Insert(value));
                Ok(edge_node)
            }
        }
    }

    /// This function works like insert in tree.rs but it also updates hashes recursively up the path
    fn build_node_recursive<'a>(
        &mut self,
        node_key: &NodeKey,
        height: usize,
        key: &BitSlice,
        value: Felt,
        path_nodes: &[(NodeKey, usize)],
        db: &mut KeyValueDB<RocksDB<BasicId>, BasicId>,
    ) -> Result<(Felt, ProofNode, ProofNodeChildren), PartialTrieError> {
        let (mut node, mut children) = self.trie.proof_nodes.get(*node_key).unwrap().clone();

        match &mut node {
            ProofNode::Edge { child, path } => {
                println!("Building edge node");
                let common = common_path(path, height as usize, key);
                println!("Key: {:?}", key);
                println!("Common: {:?}", common);
                println!("Height: {:?}", height);
                println!("Path: {:?}", path);

                let branch_height = height as usize + common.len();

                println!("Branch height: {:?}", branch_height);
                println!("Key length: {:?}", key.len());
                if branch_height >= key.len() {
                    println!("We are at the leaf node - lets update it");
                    let key_bytes = bitslice_to_bytes(key);
                    self.trie
                        .cache_leaf_modified
                        .insert(key_bytes, InsertOrRemove::Insert(value));
                    *child = value;

                    let final_hash = self.hash_up_merkle_path(key, value, path_nodes, false);
                    self.trie.proof_nodes[*node_key] = (node.clone(), children.clone());
                    return Ok((final_hash, node.clone(), children.clone()));
                }

                let child_height = branch_height + 1;
                // Path from binary node to new leaf
                let new_path = key[child_height..].to_bitvec();
                // Path from binary node to existing child
                let old_path = path[common.len() + 1..].to_bitvec();

                let (new_hash, new_id) = if new_path.is_empty() {
                    println!("New path is empty");
                    (value, None)
                } else {
                    //Children should be probably none ase they are leafs
                    let edge_hash = hash_edge_node::<H>(&Path(new_path.clone()), value);
                    let children = ProofNodeChildren::None;

                    let edge_id = self.trie.proof_nodes.insert((
                        ProofNode::Edge {
                            path: Path(new_path),
                            child: value,
                        },
                        children,
                    ));

                    (edge_hash, Some(edge_id))
                };

                println!("Children: {:?}", children);
                let old_child = match children {
                    ProofNodeChildren::None => None,
                    // ProofNodeChildren::EdgeChildrenHandle { child } => child,
                    ProofNodeChildren::BinaryChildrenHandle { left, right } => {
                        let next_direction = Direction::from(key[branch_height]);
                        match next_direction {
                            //ITS REVERSED ON PURPOSE BUT I NEED TO THINK ABOUT IT
                            // WE want here to get the opposite child to our direction
                            //thats an old child
                            Direction::Left => right,
                            Direction::Right => left,
                        }
                    }
                    _ => None,
                };

                println!("Old child: {:?}", old_child);

                let (old_hash, old_id) = if old_path.is_empty() {
                    println!("Old path is empty");
                    (*child, old_child)
                } else {
                    let edge_hash = hash_edge_node::<H>(&Path(old_path.clone()), *child);
                    //Children should be probably none as they are leafs
                    let children = ProofNodeChildren::None;
                    let edge_id = self.trie.proof_nodes.insert((
                        ProofNode::Edge {
                            path: Path(old_path),
                            child: *child,
                        },
                        children,
                    ));

                    (edge_hash, Some(edge_id))
                };

                let new_direction = Direction::from(key[branch_height]);
                let (left_child, right_child) = match new_direction {
                    Direction::Left => (new_id, old_id),
                    Direction::Right => (old_id, new_id),
                };

                let (left, right) = match new_direction {
                    Direction::Left => (new_hash, old_hash),
                    Direction::Right => (old_hash, new_hash),
                };

                let branch = ProofNode::Binary { left, right };
                let branch_hash = hash_binary_node::<H>(left, right);

                println!("Left: {:?}, Right: {:?}", left, right);
                println!(
                    "Left child: {:?}, Right child: {:?}",
                    left_child, right_child
                );

                let (current_hash, new_node, child) = if common.is_empty() {
                    //here we dont want to create new node but we want to update the old one as in set() tree.rs
                    //read below for more details
                    println!("Returning binary node ONLY {:?}", branch);
                    let binary_child = ProofNodeChildren::BinaryChildrenHandle {
                        left: left_child,
                        right: right_child,
                    };

                    (branch_hash, branch, binary_child)
                } else {
                    let edge_node_hash =
                        hash_edge_node::<H>(&Path(common.to_bitvec()), branch_hash);
                    //here we dont want to create new node but we want to update the old one as in set() tree.rs
                    //there are two cases:
                    //if common is empy we update node as binary_node
                    //else we update node as edge node, also, we need to create ProofNode structures here with updates values
                    //and then update correct NodeKey

                    //here we want to insert new node as we just created it and it will be a child of edge node as in tree.rs
                    // we will use branch_node_key as a child of higher edge node
                    let branch_node_key = self.create_binary_node(
                        branch_height,
                        left,
                        right,
                        left_child,
                        right_child,
                    )?;

                    let new_node = ProofNode::Edge {
                        path: Path(common.to_bitvec()),
                        child: branch_hash,
                    };
                    println!("Returning edge node with binary node {:?}", new_node);

                    let edge_child = ProofNodeChildren::EdgeChildrenHandle {
                        child: Some(branch_node_key),
                    };
                    (edge_node_hash, new_node, edge_child)
                };

                //these are the children of higher edge node so it should be inserted binary node
                //or if there is no higher edge node then childs should be egde nodes inserted
                //under binary node else there are leafs so children should be None as we do not insert them as nodes
                children = child;
                node = new_node;

                println!("Path nodes: {:?}\n", path_nodes);
                println!(
                    "Current hash before hash_up_merkle_path: {:?}",
                    current_hash
                );
                let final_hash = self.hash_up_merkle_path(key, current_hash, path_nodes, true);

                let key_bytes = bitslice_to_bytes(&key[..height as usize]);
                log::trace!("2 death row add ({:?})", key_bytes);
                self.trie.death_row.insert(TrieKey::Trie(key_bytes));
                Ok((final_hash, node, children))
            }
            ProofNode::Binary { left, right } => {
                let child_height = height + 1;
                let direction = Direction::from(key[height as usize]);

                if child_height as usize == key.len() {
                    println!("Building current node");
                    println!("Value: {:?}", value);
                    println!("Left: {:?}", *left);
                    println!("Right: {:?}", *right);
                    let (current_hash, new_node) = match direction {
                        Direction::Left => {
                            //we return proof node to update binary node in proof_nodes
                            let binary_node = hash_binary_node::<H>(value, *right);
                            (
                                binary_node,
                                ProofNode::Binary {
                                    left: value,
                                    right: *right,
                                },
                            )
                        }
                        Direction::Right => {
                            //we return proof node to update binary node in proof_nodes
                            let binary_node = hash_binary_node::<H>(*left, value);
                            (
                                binary_node,
                                ProofNode::Binary {
                                    left: *left,
                                    right: value,
                                },
                            )
                        }
                    };
                    let key_bytes = bitslice_to_bytes(key);
                    self.trie
                        .cache_leaf_modified
                        .insert(key_bytes, InsertOrRemove::Insert(value));

                    let new_children = ProofNodeChildren::None; // Thats a leaf so no children
                    children = new_children;
                    node = new_node;

                    let final_hash = self.hash_up_merkle_path(key, current_hash, path_nodes, true);
                    Ok((final_hash, node, children))
                } else {
                    println!("Binary node which is not at the end of the path, we should fetch the full trie");
                    Err(PartialTrieError::NodeNotFound) // This case should be handled properly
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
    ) -> Felt {
        println!("Path nodes in hash_up_merkle_path: {:?}\n", path_nodes);
        println!(
            "Initial current_hash: {:?}, height: {}",
            current_hash,
            path_nodes.last().unwrap().1
        );

        let mut nodes = path_nodes.iter().rev().skip(if skip_last { 1 } else { 0 });

        self.hash_up_recursive(key, current_hash, &mut nodes)
    }

    /// This function hashes up the path recursively
    fn hash_up_recursive<'a, I>(
        &mut self,
        key: &BitSlice,
        current_hash: Felt,
        nodes: &mut I,
    ) -> Felt
    where
        I: Iterator<Item = &'a (NodeKey, usize)>,
    {
        if let Some((node_key, height)) = nodes.next() {
            let (node, children) = self.trie.proof_nodes.get(*node_key).unwrap().clone();
            match node {
                ProofNode::Binary { left, right } => {
                    println!("PROCESSING BINARY NODE");
                    //HERE IS THE PROBLEM
                    println!("Left leaf: {:?}, Right leaf: {:?}", left, right);
                    let direction = Direction::from(key[*height as usize]);
                    let new_hash = match direction {
                        Direction::Left => {
                            let binary_node = hash_binary_node::<H>(current_hash, right);
                            println!("New binary hash (left): {:?}", binary_node);
                            self.trie.proof_nodes[*node_key] = (
                                ProofNode::Binary {
                                    left: current_hash,
                                    right: right,
                                },
                                children.clone(),
                            );
                            binary_node
                        }
                        Direction::Right => {
                            let binary_node = hash_binary_node::<H>(left, current_hash);
                            println!("New binary hash (right): {:?}", binary_node);
                            self.trie.proof_nodes[*node_key] = (
                                ProofNode::Binary {
                                    left: left,
                                    right: current_hash,
                                },
                                children.clone(),
                            );
                            binary_node
                        }
                    };
                    self.hash_up_recursive(key, new_hash, nodes)
                }
                ProofNode::Edge {
                    path: edge_path,
                    child: _,
                } => {
                    println!("PROCESSING EDGE NODE");
                    println!("Current hash: {:?}", current_hash);
                    println!("Edge path: {:?}", edge_path);
                    let edge_node = hash_edge_node::<H>(&edge_path, current_hash);
                    println!("New edge hash: {:?}", edge_node);
                    self.trie.proof_nodes[*node_key] = (
                        ProofNode::Edge {
                            path: edge_path.clone(),
                            child: current_hash,
                        },
                        children.clone(),
                    );
                    self.hash_up_recursive(key, edge_node, nodes)
                }
            }
        } else {
            println!(
                "No more nodes to process, returning current_hash: {:?}",
                current_hash
            );
            current_hash
        }
    }

    /// This function goes through the current partial tree and collects the existing elements,
    /// if the element is missing then it selects the proof from the full tree,
    /// if the tree is empty at the beginning then it completes the partial tree in full from the proof
    pub fn get_partial_path_from_existing_trie(
        &mut self,
        key: &BitSlice,
        proof: MultiProof,
        original_root: Felt,
        db: &KeyValueDB<RocksDB<BasicId>, BasicId>,
    ) -> Result<Vec<(NodeKey, usize)>, PartialTrieError> {
        let proof_keys = vec![key];
        let proof_clone = proof.clone();

        let mut iter = self.trie.iter_partial(db, proof_clone);
        let mut visitor = NoopPartialVisitor::<H>(PhantomData);

        for key in proof_keys {
            let key = key.as_ref();
            if key.len() != self.max_height as usize {
                return Err(PartialTrieError::KeyLength);
            }
            iter.traverse_to_partial::<NoopPartialVisitor<H>>(&mut visitor, key, original_root)
                .unwrap();
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
        trie::partial,
        BonsaiStorage, BonsaiStorageConfig,
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
            u8::ANY,
        )
            .prop_map(|(bits, v)| {
                let key = bits.into_iter().collect();
                let value = Felt::from(v as u64 + 100);
                (key, value)
            })
    }

    fn arb_value() -> impl Strategy<Value = Felt> {
        u8::ANY.prop_map(|v| Felt::from(v as u64 + 100))
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

    proptest! {
        #![proptest_config(ProptestConfig::default())]
        #[test]
        fn test_next_root_height_8(
            initial_keys_values in arb_power_of_two_keys(8),
        ) {
            let (removed_key, removed_value, remaining_keys_values) =
                select_random_key_value_from_initial_keys(initial_keys_values);
            test_next_root(8, remaining_keys_values, removed_key, removed_value);
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::default())]
        #[test]
        fn test_next_root_height_24(
            initial_keys_values in arb_power_of_two_keys(24),
        ) {
            let (removed_key, removed_value, remaining_keys_values) =
                select_random_key_value_from_initial_keys(initial_keys_values);
            test_next_root(24, remaining_keys_values, removed_key, removed_value);
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::default())]
        #[test]
        fn test_next_root_height_251(
            initial_keys_values in vec(arb_key_value(251), 1..50),
        ) {
            let (removed_key, removed_value, remaining_keys_values) =
                select_random_key_value_from_initial_keys(initial_keys_values);
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

    fn test_next_root(
        height: u8,
        initial_keys_values: Vec<(BitVec, Felt)>,
        new_key: BitVec,
        new_value: Felt,
    ) {
        let db = create_rocks_db(tempfile::tempdir().unwrap().path()).unwrap();
        let identifier1 = vec![1];
        let identifier2 = vec![2];
        let identifier3 = vec![3];

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
        let mut bonsai_storage3: BonsaiStorage<BasicId, RocksDB<'_, BasicId>, Pedersen> =
            BonsaiStorage::new(
                RocksDB::new(&db, RocksDBConfig::default()),
                config.clone(),
                height,
            );

        let mut id_builder = BasicIdBuilder::new();

        for (key, value) in initial_keys_values.iter() {
            bonsai_storage1.insert(&identifier1, key, value).unwrap();
            bonsai_storage2.insert(&identifier2, key, value).unwrap();
        }

        let id1 = id_builder.new_id();
        bonsai_storage1.commit(id1).unwrap();

        let current_root = bonsai_storage1.root_hash(&identifier1).unwrap();

        let tree1 = bonsai_storage1
            .tries
            .trees
            .entry(smallvec::smallvec![1])
            .or_insert_with(|| MerkleTree::new(identifier1.clone().into(), height));

        let mut proof_keys = vec![&new_key];
        let proof = tree1
            .get_multi_proof(&bonsai_storage1.tries.db, proof_keys.iter())
            .unwrap();

        let mut partial_trie =
            PartialTrie::<Pedersen>::new(identifier3.clone().into(), height, current_root);

        let (partial_path, path_nodes) = partial_trie
            .trie
            .get_partial_path(
                &bonsai_storage3.tries.db,
                proof_keys.iter(),
                proof,
                current_root,
            )
            .unwrap();
        println!("Partial path: {:?}\n", partial_path);

        let calculated_root = partial_trie
            .build_from_visited_nodes(
                path_nodes,
                &new_key,
                new_value,
                &mut bonsai_storage1.tries.db,
            )
            .unwrap();
        println!("Calculated root: {:?}", calculated_root);

        // Commit initial state of storage2
        let id2 = id_builder.new_id();
        bonsai_storage2.commit(id2).unwrap();
        println!(
            "Initial storage2 root: {:?}",
            bonsai_storage2.root_hash(&identifier2).unwrap()
        );

        // Insert new value and commit
        bonsai_storage2
            .insert(&identifier2, &new_key, &new_value)
            .unwrap();

        let id3 = id_builder.new_id();
        bonsai_storage2.commit(id3).unwrap();
        let expected_root = bonsai_storage2.root_hash(&identifier2).unwrap();
        println!("Final expected root: {:?}", expected_root);

        assert_eq!(
            calculated_root, expected_root,
            "Roots don't match: calculated={:?}, expected={:?}",
            calculated_root, expected_root
        );
    }

    #[test]
    fn test_next_root_specific_edge_cases() {
        let heights = [8, 24, 251];

        for height in heights {
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

    #[test]
    fn test_next_root_single_case() {
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
        let mut bonsai_storage3: BonsaiStorage<BasicId, RocksDB<'_, BasicId>, Pedersen> =
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
            bonsai_storage1
                .insert(&identifier, &BitVec::from_vec(key.clone()), &value)
                .unwrap();
            bonsai_storage2
                .insert(&identifier2, &BitVec::from_vec(key), &value)
                .unwrap();
        }

        let id1 = id_builder.new_id();
        bonsai_storage1.commit(id1).unwrap();
        let current_root = bonsai_storage1.root_hash(&identifier).unwrap();

        let mut new_key = vec![0; 3];
        new_key[0] = 5;
        let new_value = Felt::from(105);
        let new_key_bv = BitVec::from_vec(new_key.clone());

        let tree1 = bonsai_storage1
            .tries
            .trees
            .entry(smallvec::smallvec![1])
            .or_insert_with(|| MerkleTree::new(identifier.clone().into(), 24));

        let proof_keys = vec![&new_key_bv];
        let proof = tree1
            .get_multi_proof(&bonsai_storage1.tries.db, proof_keys.iter())
            .unwrap();

        let partial_trie_identifier = vec![3];
        let mut partial_trie =
            PartialTrie::<Pedersen>::new(partial_trie_identifier.into(), 24, current_root);

        let (partial_path, path_nodes) = partial_trie
            .trie
            .get_partial_path(
                &bonsai_storage3.tries.db,
                proof_keys.iter(),
                proof,
                current_root,
            )
            .unwrap();
        println!("Partial path: {:?}\n", partial_path);

        let calculated_root = partial_trie
            .build_from_visited_nodes(
                path_nodes,
                &new_key_bv,
                new_value,
                &mut bonsai_storage1.tries.db,
            )
            .unwrap();
        println!("Calculated root: {:?}", calculated_root);

        // Commit initial state of storage2
        let id2 = id_builder.new_id();
        bonsai_storage2.commit(id2).unwrap();
        println!(
            "Initial storage2 root: {:?}",
            bonsai_storage2.root_hash(&identifier2).unwrap()
        );

        // Insert new value and commit
        bonsai_storage2
            .insert(&identifier2, &new_key_bv, &new_value)
            .unwrap();

        let id3 = id_builder.new_id();
        bonsai_storage2.commit(id3).unwrap();
        let expected_root = bonsai_storage2.root_hash(&identifier2).unwrap();
        println!("Final expected root: {:?}", expected_root);

        assert_eq!(
            calculated_root, expected_root,
            "Roots don't match: calculated={:?}, expected={:?}",
            calculated_root, expected_root
        );
    }

    #[test]
    fn test_next_root_multiple_calls_single_test_height_8() {
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
        // let ten = bits![u8,   Msb0; 0,0,0,0,1,0,1,0];
        // let eleven = bits![u8,Msb0; 0,0,0,0,1,0,1,1];
        // let twelve = bits![u8,Msb0; 0,0,0,0,1,1,0,0];

        // let keys = vec![one, two, three, four, five, six, seven, eight, nine, ten, eleven, twelve];
        let keys = vec![one, two, three, four, five];
        let values = vec![
            Felt::from(1),
            Felt::from(2),
            Felt::from(3),
            Felt::from(4),
            Felt::from(5),
            // Felt::from(6),
            // Felt::from(7),
            // Felt::from(8),
            // Felt::from(9),
            // Felt::from(10),
            // Felt::from(11),
            // Felt::from(12),
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

        let mut partial_trie =
            PartialTrie::<Pedersen>::new(identifier4.clone().into(), 8, original_root);
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

        // println!(
        //     "Partial TRIE before updating root: {:?}\n",
        //     partial_trie.trie.proof_nodes
        // );
        // println!(
        //     "\nPartialTree NODES before updating root: {:?}\n",
        //     partial_trie
        //         .trie
        //         .proof_nodes
        //         .iter()
        //         .map(|(k, v)| (k, v))
        //         .collect::<HashMap<_, _>>()
        // );

        // let calculated_updated_root = partial_trie
        //     .set(
        //         &mut fork_tree.tries.db,
        //         one,
        //         Felt::from(13),
        //         proof_for_one,
        //         original_root,
        //     )
        //     .unwrap();
        // println!("Calculated root: {:?}\n", calculated_updated_root);

        // tree_to_compare
        //     .insert(&identifier2, one, &Felt::from(13))
        //     .unwrap();
        // tree_to_compare.commit(id_builder.new_id()).unwrap();

        // let actual_updated_root = tree_to_compare.root_hash(&identifier2).unwrap();
        // assert_eq!(
        //     calculated_updated_root, actual_updated_root,
        //     "UPDATING ROOT FAILED"
        // );
    }

    #[test]
    fn test_next_root_multiple_calls_single_test_height_24() {
        let db = create_rocks_db(tempfile::tempdir().unwrap().path()).unwrap();
        let identifier = vec![1];
        let identifier2 = vec![2];
        let identifier3 = vec![3];
        let identifier4 = vec![4];

        let config = BonsaiStorageConfig::default();
        let mut base_tree: BonsaiStorage<BasicId, RocksDB<'_, BasicId>, Pedersen> =
            BonsaiStorage::new(
                RocksDB::new(&db, RocksDBConfig::default()),
                config.clone(),
                24,
            );
        let mut tree_to_compare: BonsaiStorage<BasicId, RocksDB<'_, BasicId>, Pedersen> =
            BonsaiStorage::new(
                RocksDB::new(&db, RocksDBConfig::default()),
                config.clone(),
                24,
            );
        let mut reference_tree: BonsaiStorage<BasicId, RocksDB<'_, BasicId>, Pedersen> =
            BonsaiStorage::new(
                RocksDB::new(&db, RocksDBConfig::default()),
                config.clone(),
                24,
            );
        let mut fork_tree: BonsaiStorage<BasicId, RocksDB<'_, BasicId>, Pedersen> =
            BonsaiStorage::new(
                RocksDB::new(&db, RocksDBConfig::default()),
                config.clone(),
                24,
            );

        let mut id_builder = BasicIdBuilder::new();

        let one = bits![u8, Msb0; 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1];
        let two = bits![u8, Msb0; 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0];
        let three = bits![u8, Msb0; 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1];
        let four = bits![u8, Msb0; 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0];
        let five = bits![u8, Msb0; 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,1];
        let six = bits![u8, Msb0; 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,0];
        let seven = bits![u8, Msb0; 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1];
        let eight = bits![u8, Msb0; 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,];
        let nine = bits![u8, Msb0; 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,1];
        let ten = bits![u8, Msb0; 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0];
        let eleven = bits![u8, Msb0; 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,1];
        let twelve = bits![u8, Msb0; 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,0,0];

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

        for (key, value) in keys.iter().zip(values.iter()).take(6) {
            println!("Inserting key: {:?}", key);
            println!("Inserting value: {:?}", value);
            base_tree.insert(&identifier, key, value).unwrap();
            reference_tree.insert(&identifier3, key, value).unwrap(); // thats a referencje tree
                                                                      // println!("bonsai trie: {:?}", bonsai_storage1.tries.trees.entry(smallvec::smallvec![1]).unwrap().proof_nodes);
        }

        let id1 = id_builder.new_id();
        base_tree.commit(id1).unwrap();
        let original_root = base_tree.root_hash(&identifier).unwrap();

        let mut partial_trie =
            PartialTrie::<Pedersen>::new(identifier4.clone().into(), 24, original_root);
        let mut calculated_roots: Vec<Felt> = Vec::new();
        let mut i = 0;
        let mut current_root = original_root;

        let tree1 = base_tree
            .tries
            .trees
            .entry(smallvec::smallvec![1])
            .or_insert_with(|| MerkleTree::new(identifier.clone().into(), 24));

        for (key, value) in keys.iter().zip(values.iter()).skip(6) {
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

        //this proof is made after finishing commit of original full trie, root should be still the same
        println!("---------PROOF AFTER FINISHING COMMIT for first key -------");
        println!("{:?}\n", proof);

        let actual_root = tree_to_compare.root_hash(&identifier2).unwrap();
        assert_eq!(current_root, actual_root, "Next root calculation failed");
    }

    proptest! {
        #![proptest_config(ProptestConfig::default())]
        #[test]
        fn test_next_root_multiple_calls_height_2_only(
            initial_keys_values in arb_power_of_two_keys(2),
            new_keys_values in vec(arb_key_value(2), 1..2),
        ) {
            println!("Initial keys: {:?}", initial_keys_values);
        println!("New keys: {:?}", new_keys_values);
            test_next_root_multiple_calls(2, initial_keys_values, new_keys_values);
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::default())]
        #[test]
        fn test_next_root_multiple_calls_height_4(
            initial_keys_values in arb_power_of_two_keys(4),
            new_keys_values in vec(arb_key_value(4), 1..5),
        ) {
            test_next_root_multiple_calls(4, initial_keys_values, new_keys_values);
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::default())]
        #[test]
        fn test_next_root_multiple_calls_height_8(
            initial_keys_values in arb_power_of_two_keys(8),
            new_keys_values in vec(arb_key_value(8), 1..5),
        ) {
            test_next_root_multiple_calls(8, initial_keys_values, new_keys_values);
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::default())]
        #[test]
        fn test_next_root_multiple_calls_height_24(
            initial_keys_values in arb_power_of_two_keys(24),
            new_keys_values in vec(arb_key_value(24), 1..5),
        ) {
            test_next_root_multiple_calls(24, initial_keys_values, new_keys_values);
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::default())]
        #[test]
        fn test_next_root_multiple_calls_height_251(
            initial_keys_values in arb_power_of_two_keys(251),
            new_keys_values in vec(arb_key_value(251), 1..5),
        ) {
            test_next_root_multiple_calls(251, initial_keys_values, new_keys_values);
        }
    }

    fn test_next_root_multiple_calls(
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
        }

        base_bonsai_storage.commit(id_builder.new_id()).unwrap();
        reference_bonsai_storage
            .commit(id_builder.new_id())
            .unwrap();
        let original_root = base_bonsai_storage.root_hash(&base_identifier).unwrap();
        println!("Original root: {:?}", original_root);

        let mut partial_trie =
            PartialTrie::<Pedersen>::new(fork_identifier.clone().into(), height, original_root);

        let mut calculated_roots = Vec::new();

        let tree1 = base_bonsai_storage
            .tries
            .trees
            .entry(smallvec::smallvec![1])
            .or_insert_with(|| MerkleTree::new(base_identifier.clone().into(), height));

        let mut i = 0;
        for (key, value) in new_keys_values.iter() {
            i += 1;
            println!("ITERATION: {:?}", i);

            let proof_keys = vec![key];
            let proof = tree1
                .get_multi_proof(&base_bonsai_storage.tries.db, proof_keys.iter())
                .unwrap();

            let calculated_root = partial_trie
                .set(
                    &mut forked_bonsai_storage.tries.db,
                    key,
                    *value,
                    proof,
                    original_root,
                )
                .unwrap();
            println!("Calculated root: {:?}\n", calculated_root);

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
            assert_eq!(expected_root, actual_root);
        }
    }

    #[test]
    fn test_get_partial_path() {
        let db = create_rocks_db(tempfile::tempdir().unwrap().path()).unwrap();
        let identifier = vec![1];
        let identifier2 = vec![2];
        let identifier3 = vec![3];
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
        let mut bonsai_storage3: BonsaiStorage<BasicId, RocksDB<'_, BasicId>, Pedersen> =
            BonsaiStorage::new(
                RocksDB::new(&db, RocksDBConfig::default()),
                config.clone(),
                24,
            );

        let mut id_builder = BasicIdBuilder::new();

        for i in 0..10 {
            let mut key = vec![0; 3];
            key[0] = i;
            let value = Felt::from(i as u64 + 100);
            let key_bv = BitVec::from_vec(key.clone());

            bonsai_storage1
                .insert(&identifier, &key_bv, &value)
                .unwrap();
            bonsai_storage2
                .insert(&identifier2, &key_bv, &value)
                .unwrap();
        }

        let id1 = id_builder.new_id();
        bonsai_storage1.commit(id1).unwrap();
        let current_root = bonsai_storage1.root_hash(&identifier).unwrap();
        println!("Initial root: {:?}", current_root);

        let mut new_key = vec![0; 3];
        new_key[0] = 1;
        let new_value = Felt::from(105);
        let new_key_bv = BitVec::from_vec(new_key.clone());

        let tree1 = bonsai_storage1
            .tries
            .trees
            .entry(smallvec::smallvec![1])
            .or_insert_with(|| MerkleTree::new(identifier.clone().into(), 24));

        let proof_keys = vec![&new_key_bv];
        let proof = tree1
            .get_multi_proof(&bonsai_storage1.tries.db, proof_keys.iter())
            .unwrap();
        println!("_________________________");
        println!("FULL PROOF: {:?}\n", proof);

        let mut partial_trie =
            PartialTrie::<Pedersen>::new(identifier3.clone().into(), 24, current_root);

        // Here we get the partial path and the path nodes from original proof and the current root
        // We use the partial path to build the new partial trie below with build_from_visited_nodes().
        // We inserted new key-value pair which doesnt exist in original full trie
        // Now we have partial trie which doesn't have all the elements which are in full trie - > tree1
        // That means we have different root because it was changed by adding new key-value pair
        // some nodes in path to the root are also changed
        // We want to insert another key-value pair in the partial trie
        // But the root is different now
        // We need to get partial path and path nodes for the new key-value pair that we want to insert now
        // but we also need to construct new current_partial_nodes_heights in parrallel with  function traverse_to_partial()
        //that way we can traverse through our new partial trie but when current_partial_nodes_heights will  not have necessary nodes on the path to the leaf
        //then we should switch to the current_partial_nodes_heights constructed in parallel but on the original full trie
        //
        let (partial_path, path_nodes) = partial_trie
            .trie
            .get_partial_path(
                &bonsai_storage3.tries.db,
                proof_keys.iter(),
                proof,
                current_root,
            )
            .unwrap();
        println!("Partial path: {:?}\n", partial_path);

        let calculated_root = partial_trie
            .build_from_visited_nodes(
                path_nodes,
                &new_key_bv,
                new_value,
                &mut bonsai_storage1.tries.db,
            )
            .unwrap();
        println!("Calculated root: {:?}", calculated_root);

        // Commit initial state of storage2
        let id2 = id_builder.new_id();
        bonsai_storage2.commit(id2).unwrap();
        println!(
            "\nInitial storage2 root: {:?}\n",
            bonsai_storage2.root_hash(&identifier2).unwrap()
        );

        // Insert new value and commit
        bonsai_storage2
            .insert(&identifier2, &new_key_bv, &new_value)
            .unwrap();
        let id3 = id_builder.new_id();
        bonsai_storage2.commit(id3).unwrap();
        let expected_root = bonsai_storage2.root_hash(&identifier2).unwrap();
        println!("Final expected root: {:?}", expected_root);

        assert_eq!(
            calculated_root, expected_root,
            "Roots don't match: calculated={:?}, expected={:?}",
            calculated_root, expected_root
        );
    }

    #[test]
    fn test_get_partial_path_from_existing_trie() {
        let db = create_rocks_db(tempfile::tempdir().unwrap().path()).unwrap();
        let identifier = vec![1];
        let identifier2 = vec![2];
        let identifier3 = vec![3];
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
        let mut bonsai_storage3: BonsaiStorage<BasicId, RocksDB<'_, BasicId>, Pedersen> =
            BonsaiStorage::new(
                RocksDB::new(&db, RocksDBConfig::default()),
                config.clone(),
                24,
            );

        let mut id_builder = BasicIdBuilder::new();

        for i in 0..10 {
            let mut key = vec![0; 3];
            key[0] = i;
            let value = Felt::from(i as u64 + 100);
            let key_bv = BitVec::from_vec(key.clone());

            bonsai_storage1
                .insert(&identifier, &key_bv, &value)
                .unwrap();
            bonsai_storage2
                .insert(&identifier2, &key_bv, &value)
                .unwrap();
        }

        let id1 = id_builder.new_id();
        bonsai_storage1.commit(id1).unwrap();
        let original_root = bonsai_storage1.root_hash(&identifier).unwrap();
        println!("Initial root: {:?}", original_root);

        let mut new_key = vec![0; 3];
        new_key[0] = 1;
        let new_value = Felt::from(105);
        let new_key_bv = BitVec::from_vec(new_key.clone());

        let tree1 = bonsai_storage1
            .tries
            .trees
            .entry(smallvec::smallvec![1])
            .or_insert_with(|| MerkleTree::new(identifier.clone().into(), 24));

        let proof_keys = vec![&new_key_bv];
        let proof = tree1
            .get_multi_proof(&bonsai_storage1.tries.db, proof_keys.iter())
            .unwrap();
        println!("_________________________");
        println!("FULL PROOF: {:?}\n", proof);

        let mut partial_trie =
            PartialTrie::<Pedersen>::new(identifier3.clone().into(), 24, original_root);

        // Here we get the partial path and the path nodes from original proof and the current root
        // We use the partial path to build the new partial trie below with build_from_visited_nodes().
        // We inserted new key-value pair which doesnt exist in original full trie
        // Now we have partial trie which doesn't have all the elements which are in full trie - > tree1
        // That means we have different root because it was changed by adding new key-value pair
        // some nodes in path to the root are also changed
        // We want to insert another key-value pair in the partial trie
        // But the root is different now
        // We need to get partial path and path nodes for the new key-value pair that we want to insert now
        // but we also need to construct new current_partial_nodes_heights in parrallel with  function traverse_to_partial()
        //that way we can traverse through our new partial trie but when current_partial_nodes_heights will  not have necessary nodes on the path to the leaf
        //then we should switch to the current_partial_nodes_heights constructed in parallel but on the original full trie
        //

        let current_root = original_root;

        let path_nodes = partial_trie
            .get_partial_path_from_existing_trie(
                &new_key_bv,
                proof,
                original_root,
                &mut bonsai_storage3.tries.db,
            )
            .unwrap();
        println!("Path nodes: {:?}\n", path_nodes);
        // here i will split the path_nodes into two vectors
        // path_nodes until parameter split_index goes into build_from_visited_nodes
        let calculated_root = partial_trie
            .build_from_visited_nodes(
                path_nodes,
                &new_key_bv,
                new_value,
                &mut bonsai_storage1.tries.db,
            )
            .unwrap();
        // here another parto of path_nodes
        // let new_calculated_root = partial_trie.update_nodes

        println!("Calculated root: {:?}", calculated_root);

        // Commit initial state of storage2
        let id2 = id_builder.new_id();
        bonsai_storage2.commit(id2).unwrap();
        println!(
            "Initial storage2 root: {:?}",
            bonsai_storage2.root_hash(&identifier2).unwrap()
        );

        // Insert new value and commit
        bonsai_storage2
            .insert(&identifier2, &new_key_bv, &new_value)
            .unwrap();
        let id3 = id_builder.new_id();
        bonsai_storage2.commit(id3).unwrap();
        let expected_root = bonsai_storage2.root_hash(&identifier2).unwrap();
        println!("Final expected root: {:?}", expected_root);

        assert_eq!(
            calculated_root, expected_root,
            "Roots don't match: calculated={:?}, expected={:?}",
            calculated_root, expected_root
        );
    }

    #[test]
    fn test_next_root_height_overwriting_root() {
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
                2,
            );
        let mut reference_bonsai_storage: BonsaiStorage<BasicId, RocksDB<'_, BasicId>, Pedersen> =
            BonsaiStorage::new(
                RocksDB::new(&reference_db, RocksDBConfig::default()),
                config.clone(),
                2,
            );
        let mut fork_bonsai_storage: BonsaiStorage<BasicId, RocksDB<'_, BasicId>, Pedersen> =
            BonsaiStorage::new(
                RocksDB::new(&fork_db, RocksDBConfig::default()),
                config.clone(),
                2,
            );

        let mut id_builder = BasicIdBuilder::new();

        let three = bits![u8, Msb0; 1, 1];

        // Klucze początkowe
        let initial_keys = vec![
            three, // [1,1]
        ];

        let initial_values = vec![Felt::from(0x1)];

        for (key, value) in initial_keys.iter().zip(initial_values.iter()) {
            base_bonsai_storage
                .insert(&base_identifier, key, value)
                .unwrap();
            reference_bonsai_storage
                .insert(&reference_identifier, key, value)
                .unwrap();
        }

        base_bonsai_storage.commit(id_builder.new_id()).unwrap();
        let original_root = base_bonsai_storage.root_hash(&base_identifier).unwrap();
        println!("Original root: {:?}", original_root);

        let mut partial_trie =
            PartialTrie::<Pedersen>::new(fork_identifier.clone().into(), 2, original_root);

        let tree1 = base_bonsai_storage
            .tries
            .trees
            .entry(smallvec::smallvec![base_identifier[0]])
            .or_insert_with(|| MerkleTree::new(base_identifier.clone().into(), 2));

        // Nowy klucz do dodania - ten sam co w oryginalnym teście
        let new_key = bits![u8, Msb0; 1, 1]; // [1,1]
        let new_value = Felt::from(0x1); // 260

        let proof_keys = vec![&new_key];
        let proof = tree1
            .get_multi_proof(&base_bonsai_storage.tries.db, proof_keys.iter())
            .unwrap();
        println!("Proof: {:?}", proof);

        let calculated_root = partial_trie
            .set(
                &mut fork_bonsai_storage.tries.db,
                &new_key,
                new_value,
                proof,
                original_root,
            )
            .unwrap();
        println!("Calculated root: {:?}", calculated_root);

        // Dodaj nowy klucz do referencyjnego drzewa
        reference_bonsai_storage
            .insert(&reference_identifier, &new_key, &new_value)
            .unwrap();
        reference_bonsai_storage
            .commit(id_builder.new_id())
            .unwrap();
        let expected_root = reference_bonsai_storage
            .root_hash(&reference_identifier)
            .unwrap();
        println!("Expected root: {:?}", expected_root);

        assert_eq!(calculated_root, expected_root);
    }
}
