use super::{
    merkle_node::{hash_binary_node, hash_edge_node, BinaryNode, Direction, EdgeNode, Node},
    path::Path,
    tree::{MerkleTree, NodeKey, RootHandle},
};
use crate::databases::RocksDB;
use crate::hash_map;
use crate::id::BasicId;
use crate::trie::proof::common_path;
use crate::trie::proof::ProofVerificationError;
use crate::trie::tree::bitslice_to_bytes;
use crate::trie::tree::InsertOrRemove;
use crate::trie::trie_db::TrieKeyType;
use crate::trie::TrieKey;
use crate::BonsaiStorageError;
use crate::ByteVec;
use crate::Id;
use crate::MultiProof;
use crate::ProofNode;
use crate::{trie::merkle_node::NodeHandle, BitSlice, BitVec};
use crate::{BonsaiDatabase, KeyValueDB};
use core::marker::PhantomData;
use parity_scale_codec::Decode;
use starknet_types_core::{felt::Felt, hash::StarkHash};
use std::collections::HashMap;

#[derive(Debug, thiserror::Error)]
pub enum PartialTrieError {
    #[error(transparent)]
    ProofVerificationError(#[from] ProofVerificationError),
}

pub(crate) struct FullTrieVisitor<H: StarkHash> {
    path_nodes: Vec<(ProofNode, u64)>,
    current_path: BitVec,
    current_felt: Felt,
    _hasher: PhantomData<H>,
}

pub(crate) struct PartialTrieVisitor<H: StarkHash> {
    path_nodes: Vec<(ProofNode, u64)>,
    current_path: BitVec,
    current_felt: Felt,
    _hasher: PhantomData<H>,
}

impl<H: StarkHash> NextRootVisitor<H> for FullTrieVisitor<H> {
    fn visit_proof_nodes(
        &mut self,
        node: &ProofNode,
        path: &BitSlice,
    ) -> Result<VisitResult, PartialTrieError> {
        let height = self.current_path.len();

        if height >= path.len() {
            println!("Height is greater than path length");
            return Ok(VisitResult::Break);
        }

        match node {
            ProofNode::Binary { left, right } => {
                let direction = Direction::from(path[height]);
                self.current_path.push(direction.into());
                self.current_felt = match direction {
                    Direction::Left => *left,
                    Direction::Right => *right,
                };
                self.path_nodes.push((node.clone(), height as u64));
                Ok(VisitResult::Continue)
            }
            ProofNode::Edge {
                child,
                path: edge_path,
            } => {
                if height + edge_path.len() > path.len() {
                    println!("Height + edge_path.len() is greater than path length");
                    return Ok(VisitResult::Break);
                }
                // if path.get(height..(height + edge_path.len())) != Some(&edge_path.0) {
                //     return Ok(VisitResult::Break);
                // }
                self.current_path.extend_from_bitslice(&edge_path.0);
                self.current_felt = *child;
                self.path_nodes.push((node.clone(), height as u64));
                Ok(VisitResult::Continue)
            }
        }
    }
}

pub(crate) trait NextRootVisitor<H: StarkHash> {
    fn visit_proof_nodes(
        &mut self,
        node: &ProofNode,
        path: &BitSlice,
    ) -> Result<VisitResult, PartialTrieError>;
}

impl<H: StarkHash> NextRootVisitor<H> for PartialTrieVisitor<H> {
    fn visit_proof_nodes(
        &mut self,
        node: &ProofNode,
        path: &BitSlice,
    ) -> Result<VisitResult, PartialTrieError> {
        // we need to add here only the nodes from partial proof and from original proof
        // that are not in the partial proof
        let height = self.current_path.len();

        if height >= path.len() {
            println!("Height is greater than path length");
            return Ok(VisitResult::Break);
        }

        match node {
            ProofNode::Binary { left, right } => {
                let direction = Direction::from(path[height]);
                self.current_path.push(direction.into());
                self.current_felt = match direction {
                    Direction::Left => *left,
                    Direction::Right => *right,
                };
                self.path_nodes.push((node.clone(), height as u64));
                Ok(VisitResult::Continue)
            }
            ProofNode::Edge {
                child,
                path: edge_path,
            } => {
                if height + edge_path.len() > path.len() {
                    println!("Height + edge_path.len() is greater than path length");
                    return Ok(VisitResult::Break);
                }

                if path.get(height..(height + edge_path.len())) != Some(&edge_path.0) {
                    println!("Divergence point where to add new value to partial trie");
                    return Ok(VisitResult::Break);
                }
                self.current_path.extend_from_bitslice(&edge_path.0);
                self.current_felt = *child;
                self.path_nodes.push((node.clone(), height as u64));
                Ok(VisitResult::Continue)
            }
        }
    }
}

struct PartialTrie<H: StarkHash> {
    trie: MerkleTree<H>,
    max_height: u8,
    original_root: Felt,
    node_keys: Vec<NodeKey>,
    _hasher: PhantomData<H>,
}

impl<H: StarkHash + Send + Sync> PartialTrie<H> {
    fn new(identifier: ByteVec, max_height: u8, original_root: Felt) -> Self {
        Self {
            trie: MerkleTree::new(identifier, max_height),
            max_height,
            original_root,
            node_keys: Vec::new(),
            _hasher: PhantomData,
        }
    }

    pub fn next_root(
        &mut self,
        key: &BitSlice,
        value: Felt,
        current_root: Felt,
        proof: MultiProof,
        db: &mut KeyValueDB<RocksDB<BasicId>, BasicId>,
    ) -> Result<Felt, PartialTrieError> {
        assert!(
            key.len() == self.max_height as usize,
            "Key length mismatch: key length is {} but max height is {}",
            key.len(),
            self.max_height
        );

        let proof_keys = vec![key];
        let partial_proof = self.trie.get_multi_proof(&db, proof_keys.iter()).unwrap();

        let mut full_visitor = FullTrieVisitor::<H> {
            path_nodes: Vec::new(),
            current_path: BitVec::new(),
            current_felt: self.original_root,
            _hasher: PhantomData,
        };

        let mut partial_visitor = PartialTrieVisitor::<H> {
            path_nodes: Vec::new(),
            current_path: BitVec::new(),
            current_felt: current_root,
            _hasher: PhantomData,
        };

        // Always traverse the full tree
        let mut current_full_felt = self.original_root;
        while full_visitor.current_path.len() < key.len() {
            let Some(node) = proof.0.get(&current_full_felt) else {
                break;
            };

            match full_visitor.visit_proof_nodes(node, key)? {
                VisitResult::Continue => {
                    current_full_felt = full_visitor.current_felt;
                }
                VisitResult::Break => break,
            }
        }
        println!(
            "Full visitor path nodes after traversal: {:?}",
            full_visitor.path_nodes
        );

        // Now traverse the partial trie
        let mut current_partial_felt = current_root;
        while partial_visitor.current_path.len() < key.len() {
            let partial_result: Result<bool, PartialTrieError> =
                if let Some(node) = partial_proof.0.get(&current_partial_felt) {
                    match partial_visitor.visit_proof_nodes(node, key)? {
                        VisitResult::Continue => {
                            current_partial_felt = partial_visitor.current_felt;
                            Ok(true)
                        }
                        VisitResult::Break => Ok(false),
                    }
                } else {
                    Ok(false)
                };

            // If we encounter a missing node
            if !partial_result? {
                // Find the corresponding node in full_visitor
                if let Some((last_node, last_height)) = full_visitor.path_nodes.last() {
                    let current_partial_trie_height = partial_visitor.current_path.len();

                    if current_partial_trie_height == 0 {
                        if let Some(node) = partial_proof.0.get(&current_root) {
                            println!("Adding root node to partial visitor path nodes: {:?}", node);
                            partial_visitor.path_nodes.push((node.clone(), 0));
                        }
                    }

                    // Get all nodes down from this point
                    for (node, height) in full_visitor
                        .path_nodes
                        .iter()
                        .skip_while(|(_, height)| *height < current_partial_trie_height as u64)
                    //skip nodes until we reach the height of the partial trie
                    {
                        if *height == 0 {
                            //leave root of partial trie as it is
                            break;
                        }
                        println!(
                            "Node: {:?}, Height: {:?}, Current partial trie height: {:?}",
                            node, height, current_partial_trie_height
                        );
                        println!(
                            "Partial visitor path nodes before adding nodes: {:?}",
                            partial_visitor.path_nodes
                        );
                        partial_visitor.path_nodes.push((node.clone(), *height));
                    }
                } else {
                    println!("No nodes found in both full and partial trie");
                    break;
                }
                break;
            }
        }
        println!(
            "Partial visitor path nodes after adding nodes: {:?}",
            partial_visitor.path_nodes
        );

        let root = self.build_from_visited_nodes(partial_visitor.path_nodes, key, value, db)?;
        // self.commit(db).unwrap();
        println!(
            "Root node of a trie, should Some: {:?}",
            self.trie.root_node
        );

        let merkle_tree_root = self.trie.root_hash(db).unwrap();

        // assert_eq!(
        //     root, merkle_tree_root,
        //     "Merkle tree root hash calculation failed"
        // );
        Ok(root)
    }

    fn build_from_visited_nodes(
        &mut self,
        path_nodes: Vec<(ProofNode, u64)>,
        key: &BitSlice,
        value: Felt,
        db: &mut KeyValueDB<RocksDB<BasicId>, BasicId>,
    ) -> Result<Felt, PartialTrieError> {
        let key_bytes = bitslice_to_bytes(key);
        let mut cache_leaf_entry = self.trie.cache_leaf_modified.entry_ref(&key_bytes[..]);

        if let hash_map::EntryRef::Occupied(entry) = &mut cache_leaf_entry {
            if matches!(entry.get(), InsertOrRemove::Insert(_)) {
                println!("Value already exists in cache_leaf_modified");
                entry.insert(InsertOrRemove::Insert(value));
                return Ok(self.hash_up_merkle_path(key, value, &path_nodes, false));
            }
        }

        if let Some(value_db) = db
            .get(&TrieKey::new(
                &self.trie.identifier,
                TrieKeyType::Flat,
                &key_bytes,
            ))
            .unwrap()
        {
            if value == Felt::decode(&mut value_db.as_slice()).unwrap() {
                return Ok(self.trie.root_hash(db).unwrap());
            }
        }

        match path_nodes.last() {
            Some((node, height)) => match node {
                ProofNode::Edge { child, path } => {
                    let common = common_path(path, *height as usize, key);
                    let branch_height = *height as usize + common.len();

                    // If we are at the leaf, we can just update the value and hash up the tree
                    if branch_height >= key.len() {
                        println!("Branch height is greater than key length");
                        self.trie
                            .cache_leaf_modified
                            .insert(key_bytes, InsertOrRemove::Insert(value));
                        return Ok(self.hash_up_merkle_path(key, value, &path_nodes, false));
                    }

                    let split = PathSplit::<H>::from_edge_and_key(
                        path,
                        *child,
                        key,
                        value,
                        common,
                        *height as usize,
                    );

                    self.trie
                        .cache_leaf_modified
                        .insert(key_bytes, InsertOrRemove::Insert(value));

                    let binary_node = split.create_binary_node_hash();

                    let node_id = self.trie.insert_binary_node(
                        branch_height as u64,
                        split.new_branch.value,
                        split.old_branch.value,
                        binary_node,
                    )?;

                    self.node_keys.push(node_id);

                    let current_hash = if common.is_empty() {
                        binary_node
                    } else {
                        let edge_node = hash_edge_node::<H>(
                            &Path(path.0[..common.len()].to_bitvec()),
                            binary_node,
                        );
                        let node_id = self.trie.insert_edge_node(
                            *height,
                            &Path(path.0[..common.len()].to_bitvec()),
                            binary_node,
                            edge_node,
                            key,
                        )?;
                        self.node_keys.push(node_id);

                        edge_node
                    };

                    let final_hash = self.hash_up_merkle_path(
                        key,
                        current_hash,
                        &path_nodes,
                        true, // Skip last node only if it's not the root
                    );
                    let key_bytes = bitslice_to_bytes(&key[..*height as usize]);
                    self.trie.death_row.insert(TrieKey::Trie(key_bytes));
                    Ok(final_hash)
                }
                ProofNode::Binary { left, right } => {
                    let direction = Direction::from(key[*height as usize]);
                    let current_hash = match direction {
                        Direction::Left => {
                            let binary_node = hash_binary_node::<H>(value, *right);

                            let node_id = self.trie.insert_binary_node(
                                *height,
                                value,
                                *right,
                                binary_node,
                            )?;
                            self.node_keys.push(node_id);

                            binary_node
                        }
                        Direction::Right => {
                            let binary_node = hash_binary_node::<H>(*left, value);

                            let node_id =
                                self.trie
                                    .insert_binary_node(*height, *left, value, binary_node)?;
                            self.node_keys.push(node_id);

                            binary_node
                        }
                    };
                    self.trie
                        .cache_leaf_modified
                        .insert(key_bytes, InsertOrRemove::Insert(value));
                    let final_hash = self.hash_up_merkle_path(
                        key,
                        current_hash,
                        &path_nodes,
                        true, // Skip last node only if it's not the root
                    );
                    Ok(final_hash)
                }
            },
            None => {
                let edge_node = hash_edge_node::<H>(&Path(key.to_bitvec()), value);

                let node_id =
                    self.trie
                        .insert_edge_node(0, &Path(key.to_bitvec()), value, edge_node, key)?;
                self.node_keys.push(node_id);

                println!("Inserted root node!: {:?}", node_id);
                // self.trie.root_node = Some(RootHandle::Loaded(node_id));

                self.trie
                    .cache_leaf_modified
                    .insert(key_bytes, InsertOrRemove::Insert(value));
                Ok(edge_node)
            }
        }
    }

    pub fn commit<DB: BonsaiDatabase, ID: Id>(
        &mut self,
        db: &mut KeyValueDB<DB, ID>,
    ) -> Result<(), BonsaiStorageError<DB::DatabaseError>> {
        let db_changes = self.trie.get_updates::<DB>()?;

        let mut batch = db.create_batch();
        for (key, value) in db_changes {
            match value {
                InsertOrRemove::Insert(value) => {
                    db.insert(&key, &value, Some(&mut batch))?;
                }
                InsertOrRemove::Remove => {
                    db.remove(&key, Some(&mut batch))?;
                }
            }
        }
        db.write_batch(batch)?;
        Ok(())
    }

    pub fn root_hash<DB: BonsaiDatabase, ID: Id>(
        &self,
        db: &KeyValueDB<DB, ID>,
    ) -> Result<Felt, BonsaiStorageError<DB::DatabaseError>> {
        self.trie.root_hash(db)
    }

    fn get_node_hash(&self, handle: &NodeHandle) -> Felt {
        match handle {
            NodeHandle::Hash(hash) => *hash,
            NodeHandle::InMemory(_) => {
                // TODO: lazily load node from proof
                unimplemented!()
            }
        }
    }

    fn hash_up_merkle_path(
        &mut self,
        key: &BitSlice,
        mut current_hash: Felt,
        path_nodes: &[(ProofNode, u64)],
        skip_last: bool, // whether to skip the last element (e.g. if it has already been processed)
    ) -> Felt {
        let iter = path_nodes.iter().rev().skip(if skip_last { 1 } else { 0 });

        for (node, height) in iter {
            match node {
                ProofNode::Binary { left, right } => {
                    let direction = Direction::from(key[*height as usize]);
                    current_hash = match direction {
                        Direction::Left => {
                            let binary_node = hash_binary_node::<H>(current_hash, *right);

                            let node_id = self
                                .trie
                                .insert_binary_node(*height, current_hash, *right, binary_node)
                                .unwrap();
                            self.node_keys.push(node_id);

                            binary_node
                        }
                        Direction::Right => {
                            let binary_node = hash_binary_node::<H>(*left, current_hash);

                            let node_id = self
                                .trie
                                .insert_binary_node(*height, *left, current_hash, binary_node)
                                .unwrap();
                            self.node_keys.push(node_id);

                            binary_node
                        }
                    };
                }
                ProofNode::Edge {
                    path: edge_path,
                    child: _,
                } => {
                    let edge_node = hash_edge_node::<H>(edge_path, current_hash);

                    let node_id = self
                        .trie
                        .insert_edge_node(*height, edge_path, current_hash, edge_node, key)
                        .unwrap();
                    self.node_keys.push(node_id);

                    current_hash = edge_node;
                }
            }
        }

        // self.update_node_references();
        // println!("NODE KEYS: {:?}", self.node_keys);

        current_hash
    }

    fn update_node_references(&mut self) {
        let mut hash_to_node: HashMap<Felt, NodeKey> = HashMap::new();

        for node_key in &self.node_keys {
            if let Some(node) = self.trie.nodes.get(*node_key) {
                if let Some(hash) = node.get_hash() {
                    hash_to_node.insert(hash, *node_key);
                }
            }
        }

        for node_key in &self.node_keys {
            if let Some(node) = self.trie.nodes.get_mut(*node_key) {
                match node {
                    Node::Binary(binary) => {
                        if let NodeHandle::Hash(left_hash) = binary.left {
                            if let Some(&left_node_key) = hash_to_node.get(&left_hash) {
                                binary.left = NodeHandle::InMemory(left_node_key);
                            }
                        }

                        if let NodeHandle::Hash(right_hash) = binary.right {
                            if let Some(&right_node_key) = hash_to_node.get(&right_hash) {
                                binary.right = NodeHandle::InMemory(right_node_key);
                            }
                        }
                    }
                    Node::Edge(edge) => {
                        if let NodeHandle::Hash(child_hash) = edge.child {
                            if let Some(&child_node_key) = hash_to_node.get(&child_hash) {
                                edge.child = NodeHandle::InMemory(child_node_key);
                            }
                        }
                    }
                }
            }
        }
    }
}

#[derive(Debug, Clone)]
struct PathSplit<H: StarkHash> {
    common_prefix: Path,
    key: BitVec,
    branch_height: u64,
    new_branch: PathBranch,
    old_branch: PathBranch,
    _hasher: PhantomData<H>,
}

#[derive(Debug)]
pub(crate) enum VisitResult {
    Continue,
    Break,
}

#[derive(Debug, Clone)]
struct PathBranch {
    path: Path,
    value: Felt,
}

impl<H: StarkHash> PathSplit<H> {
    fn from_edge_and_key(
        edge_path: &Path,
        edge_value: Felt,
        key: &BitSlice,
        new_value: Felt,
        common: &BitSlice,
        height: usize,
    ) -> Self {
        let branch_height = height + common.len();
        let child_height = branch_height + 1;

        Self {
            common_prefix: Path(common.to_bitvec()),
            key: key.to_bitvec(),
            branch_height: branch_height as u64,
            new_branch: PathBranch {
                path: Path(key[child_height..].to_bitvec()),
                value: new_value,
            },
            old_branch: PathBranch {
                path: Path(edge_path.0[common.len() + 1..].to_bitvec()),
                value: edge_value,
            },
            _hasher: PhantomData,
        }
    }

    fn create_binary_node_hash(&self) -> Felt {
        let new_hash = if self.new_branch.path.is_empty() {
            self.new_branch.value
        } else {
            hash_edge_node::<H>(&self.new_branch.path, self.new_branch.value)
        };

        let old_hash = if self.old_branch.path.is_empty() {
            self.old_branch.value
        } else {
            hash_edge_node::<H>(&self.old_branch.path, self.old_branch.value)
        };

        let new_direction = Direction::from(self.key[self.branch_height as usize]);

        match new_direction {
            Direction::Left => hash_binary_node::<H>(new_hash, old_hash),
            Direction::Right => hash_binary_node::<H>(old_hash, new_hash),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        databases::{create_rocks_db, RocksDB, RocksDBConfig},
        id::{BasicId, BasicIdBuilder},
        BonsaiStorage, BonsaiStorageConfig,
    };
    use bitvec::prelude::Msb0;
    use proptest::collection::vec;
    use proptest::num::u8;
    use proptest::prelude::*;
    use starknet_types_core::hash::Pedersen;

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

        // Calculate next root using PartialTrie
        let mut partial_trie =
            PartialTrie::<Pedersen>::new(identifier1.into(), height, current_root);
        let next_root = partial_trie
            .next_root(
                &new_key,
                new_value,
                current_root,
                proof,
                &mut bonsai_storage1.tries.db,
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

        let actual_root = bonsai_storage2.root_hash(&identifier2).unwrap();

        assert_eq!(next_root, actual_root);
    }

    // Test for specific edge cases
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

    // Single test case from proof.rs
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
            .or_insert_with(|| MerkleTree::new(identifier.clone().into(), 24));

        let proof_keys = vec![&new_key_bv];
        let proof = tree1
            .get_multi_proof(&bonsai_storage1.tries.db, proof_keys.iter())
            .unwrap();

        let partial_trie_identifier = vec![3];
        // Calculate next root using PartialTrie
        let mut partial_trie =
            PartialTrie::<Pedersen>::new(partial_trie_identifier.into(), 24, current_root);
        let next_root = partial_trie
            .next_root(
                &new_key_bv,
                new_value,
                current_root,
                proof,
                &mut bonsai_storage1.tries.db,
            )
            .unwrap();

        let id2 = id_builder.new_id();
        bonsai_storage2.commit(id2).unwrap();
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

    #[test]
    fn test_next_root_multiple_calls_single_test() {
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

        let mut keys = Vec::new();
        let mut values = Vec::new();
        for i in 1..=5 {
            let mut key = vec![0; 3];
            key[0] = i;
            let value = Felt::from(i as u64 + 100);
            keys.push(BitVec::from_vec(key));
            values.push(value);
        }

        for (key, value) in keys.iter().zip(values.iter()).take(3) {
            bonsai_storage1.insert(&identifier, key, value).unwrap();
        }

        let id1 = id_builder.new_id();
        bonsai_storage1.commit(id1).unwrap();
        let mut current_root = bonsai_storage1.root_hash(&identifier).unwrap();

        let mut partial_trie =
            PartialTrie::<Pedersen>::new(identifier.clone().into(), 24, current_root);
        let mut next_roots = Vec::new();
        let mut i = 0;
        for (key, value) in keys.iter().zip(values.iter()).skip(3) {
            let tree1 = bonsai_storage1
                .tries
                .trees
                .entry(smallvec::smallvec![1])
                .or_insert_with(|| MerkleTree::new(identifier.clone().into(), 24));

            let proof_keys = vec![key];
            let proof = tree1
                .get_multi_proof(&bonsai_storage1.tries.db, proof_keys.iter())
                .unwrap();

            i += 1;
            println!("ITERATION: {:?}", i);

            let next_root = partial_trie
                .next_root(
                    key,
                    *value,
                    current_root,
                    proof,
                    &mut bonsai_storage1.tries.db,
                )
                .unwrap();

            next_roots.push(next_root);
            current_root = next_root;
        }
        println!("--------------------------------");
        println!("Partial TRIE: {:?}", partial_trie.trie);
        println!("--------------------------------");

        for (key, value) in keys.iter().zip(values.iter()) {
            bonsai_storage2.insert(&identifier2, key, value).unwrap();
        }

        bonsai_storage2.commit(id_builder.new_id()).unwrap();

        let actual_root = bonsai_storage2.root_hash(&identifier2).unwrap();
        assert_eq!(current_root, actual_root, "Next root calculation failed");
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
        let db = create_rocks_db(tempfile::tempdir().unwrap().path()).unwrap();
        let identifier = vec![1];
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

        for (key, value) in initial_keys_values.iter() {
            bonsai_storage1.insert(&identifier, key, value).unwrap();
            bonsai_storage2.insert(&identifier2, key, value).unwrap();
        }

        let id1 = id_builder.new_id();
        bonsai_storage1.commit(id1).unwrap();
        let current_root = bonsai_storage1.root_hash(&identifier).unwrap();

        let mut partial_trie =
            PartialTrie::<Pedersen>::new(identifier.clone().into(), height, current_root);
        let mut current_root = current_root;
        let mut next_roots = Vec::new();

        for (key, value) in new_keys_values.iter() {
            let tree1 = bonsai_storage1
                .tries
                .trees
                .entry(smallvec::smallvec![1])
                .or_insert_with(|| MerkleTree::new(identifier.clone().into(), height));

            let proof_keys = vec![key];
            let proof = tree1
                .get_multi_proof(&bonsai_storage1.tries.db, proof_keys.iter())
                .unwrap();

            let next_root = partial_trie
                .next_root(
                    key,
                    *value,
                    current_root,
                    proof,
                    &mut bonsai_storage1.tries.db,
                )
                .unwrap();

            // bonsai_storage1.insert(&identifier, key, value).unwrap();
            // bonsai_storage1.commit(id_builder.new_id()).unwrap();

            next_roots.push(next_root);
            current_root = next_root;
        }

        for ((key, value), expected_root) in new_keys_values.iter().zip(next_roots) {
            bonsai_storage2.insert(&identifier2, key, value).unwrap();
            bonsai_storage2.commit(id_builder.new_id()).unwrap();

            let actual_root = bonsai_storage2.root_hash(&identifier2).unwrap();
            assert_eq!(expected_root, actual_root);
        }
    }

    #[test]
    fn test_how_commit_works() {
        let db = create_rocks_db(tempfile::tempdir().unwrap().path()).unwrap();
        let identifier = vec![1];
        let config = BonsaiStorageConfig::default();

        let mut bonsai_storage: BonsaiStorage<BasicId, RocksDB<'_, BasicId>, Pedersen> =
            BonsaiStorage::new(
                RocksDB::new(&db, RocksDBConfig::default()),
                config.clone(),
                24,
            );
        let mut id_builder = BasicIdBuilder::new();

        let mut keys = Vec::new();
        let mut values = Vec::new();
        for i in 1..=5 {
            let mut key = vec![0; 3];
            key[0] = i;
            let value = Felt::from(i as u64 + 100);
            keys.push(BitVec::from_vec(key));
            values.push(value);
        }

        for (key, value) in keys.iter().zip(values.iter()).take(3) {
            println!("__________Initial insertions__________");
            bonsai_storage.insert(&identifier, key, value).unwrap();
        }
        bonsai_storage.commit(id_builder.new_id()).unwrap();

        for (key, value) in keys.iter().zip(values.iter()).skip(3) {
            println!("__________Insertion of new key-value__________");
            bonsai_storage.insert(&identifier, key, value).unwrap();
            println!("__________End of insertion of new key-value__________");
            bonsai_storage.commit(id_builder.new_id()).unwrap();
        }
    }
}
