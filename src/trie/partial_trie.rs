use super::{
    merkle_node::{hash_binary_node, hash_edge_node, Direction},
    path::Path,
    tree::MerkleTree,
};
use crate::databases::RocksDB;
use crate::id::BasicId;
use crate::trie::proof::common_path;
use crate::trie::proof::ProofVerificationError;
use crate::trie::tree::InsertOrRemove;
use crate::BonsaiStorageError;
use crate::ByteVec;
use crate::Id;
use crate::MultiProof;
use crate::ProofNode;
use crate::{trie::merkle_node::NodeHandle, BitSlice, BitVec};
use crate::{BonsaiDatabase, KeyValueDB};
use core::marker::PhantomData;
use starknet_types_core::{felt::Felt, hash::StarkHash};

#[derive(Debug, thiserror::Error)]
pub enum PartialTrieError {
    #[error(transparent)]
    ProofVerificationError(#[from] ProofVerificationError),
}
pub(crate) trait PartialTrieVisitor<H: StarkHash> {
    fn visit_proof_nodes(
        &mut self,
        node: &ProofNode,
        path: &BitSlice,
        height: usize,
    ) -> Result<VisitResult, PartialTrieError>;

    fn update_path_and_felt(&mut self, path: &BitSlice, height: usize, node: &ProofNode);
}

pub(crate) struct NextRootVisitor<H: StarkHash> {
    path_nodes: Vec<(ProofNode, u64)>,
    current_path: BitVec,
    current_felt: Felt,
    _hasher: PhantomData<H>,
}

impl<H: StarkHash> PartialTrieVisitor<H> for NextRootVisitor<H> {
    fn visit_proof_nodes(
        &mut self,
        node: &ProofNode,
        path: &BitSlice,
        height: usize,
    ) -> Result<VisitResult, PartialTrieError> {
        self.path_nodes.push((node.clone(), height as u64));

        match node {
            ProofNode::Binary { left, right } => {
                let direction = Direction::from(path[height]);
                self.current_path.push(direction.into());
                self.current_felt = match direction {
                    Direction::Left => *left,
                    Direction::Right => *right,
                };
                Ok(VisitResult::Continue)
            }
            ProofNode::Edge {
                child,
                path: edge_path,
            } => {
                if path.get(height..(height + edge_path.len())) != Some(&edge_path.0) {
                    return Ok(VisitResult::Break);
                }
                self.current_path.extend_from_bitslice(&edge_path.0);
                self.current_felt = *child;
                Ok(VisitResult::Continue)
            }
        }
    }

    fn update_path_and_felt(&mut self, path: &BitSlice, height: usize, node: &ProofNode) {
        match node {
            ProofNode::Binary { left, right } => {
                let direction = Direction::from(path[height]);
                self.current_path.push(direction.into());
                self.current_felt = match direction {
                    Direction::Left => *left,
                    Direction::Right => *right,
                };
            }
            ProofNode::Edge {
                child,
                path: edge_path,
            } => {
                self.current_path.extend_from_bitslice(&edge_path.0);
                self.current_felt = *child;
            }
        }
    }
}

struct PartialTrie<H: StarkHash> {
    trie: MerkleTree<H>,
    max_height: u8,
    _hasher: PhantomData<H>,
}

impl<H: StarkHash + Send + Sync> PartialTrie<H> {
    fn new(identifier: ByteVec, max_height: u8) -> Self {
        Self {
            trie: MerkleTree::new(identifier, max_height),
            max_height,
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

        //Proof from partial trie
        let proof_keys = vec![key];
        let partial_proof = self.trie.get_multi_proof(&db, proof_keys.iter()).unwrap();

        let mut visitor = NextRootVisitor::<H> {
            path_nodes: Vec::new(),
            current_path: BitVec::new(),
            current_felt: current_root,
            _hasher: PhantomData,
        };

        let mut current_felt = current_root;
        loop {
            if visitor.current_path.len() == key.len() {
                break;
            }

            let Some(node) = proof.0.get(&current_felt) else {
                break;
            };

            match visitor.visit_proof_nodes(node, key, visitor.current_path.len())? {
                VisitResult::Continue => {
                    current_felt = visitor.current_felt;
                }
                VisitResult::Break => {
                    break;
                }
            }
        }
        let root = self.build_from_visited_nodes(visitor.path_nodes, key, value)?;

        //Can't commit here because we need to check the root hash after the commit
        //After commit rooth hash is set to NONE and we can't get it

        // self.commit(db).unwrap();

        let merkle_tree_root_after_commit = self.trie.root_hash(db).unwrap();
        assert_eq!(
            root, merkle_tree_root_after_commit,
            "Merkle tree root hash calculation failed"
        );
        Ok(root)
    }

    fn build_from_visited_nodes(
        &mut self,
        path_nodes: Vec<(ProofNode, u64)>,
        key: &BitSlice,
        value: Felt,
    ) -> Result<Felt, PartialTrieError> {
        // let key_bytes = bitslice_to_bytes(key);
        // self.trie.cache_leaf_modified.insert(key_bytes, InsertOrRemove::Insert(value));

        match path_nodes.last() {
            Some((node, height)) => match node {
                ProofNode::Edge { child, path } => {
                    let common = common_path(path, *height as usize, key);
                    let branch_height = *height as usize + common.len();

                    // If we are at the leaf, we can just update the value and hash up the tree
                    if branch_height >= key.len() {
                        return Ok(hash_up_merkle_path::<H>(
                            key,
                            value,
                            &path_nodes,
                            false,
                            &mut self.trie,
                        ));
                    }

                    let split = PathSplit::<H>::from_edge_and_key(
                        path,
                        *child,
                        key,
                        value,
                        common,
                        *height as usize,
                    );

                    let binary_node = split.create_binary_node_hash();

                    self.trie.insert_binary_node(
                        branch_height as u64,
                        split.new_branch.value,
                        split.old_branch.value,
                        binary_node,
                    )?;

                    let current_hash = if common.is_empty() {
                        binary_node
                    } else {
                        self.trie.insert_edge_node(
                            *height,
                            &Path(path.0[..common.len()].to_bitvec()),
                            binary_node,
                            hash_edge_node::<H>(
                                &Path(path.0[..common.len()].to_bitvec()),
                                binary_node,
                            ),
                        )?;
                        hash_edge_node::<H>(&Path(path.0[..common.len()].to_bitvec()), binary_node)
                    };

                    let final_hash = hash_up_merkle_path::<H>(
                        key,
                        current_hash,
                        &path_nodes,
                        true,
                        &mut self.trie,
                    );
                    // println!("__________________________");
                    // println!("trie: {:?}", self.trie);
                    // println!("__________________________");
                    Ok(final_hash)
                }
                ProofNode::Binary { left, right } => {
                    let direction = Direction::from(key[*height as usize]);
                    let current_hash = match direction {
                        Direction::Left => {
                            let binary_node = hash_binary_node::<H>(value, *right);
                            self.trie
                                .insert_binary_node(*height, value, *right, binary_node)?;
                            binary_node
                        }
                        Direction::Right => {
                            let binary_node = hash_binary_node::<H>(*left, value);
                            self.trie
                                .insert_binary_node(*height, *left, value, binary_node)?;
                            binary_node
                        }
                    };
                    let final_hash = hash_up_merkle_path::<H>(
                        key,
                        current_hash,
                        &path_nodes,
                        true,
                        &mut self.trie,
                    );
                    Ok(final_hash)
                }
            },
            None => {
                let edge_node = hash_edge_node::<H>(&Path(key.to_bitvec()), value);
                self.trie
                    .insert_edge_node(0, &Path(key.to_bitvec()), value, edge_node)?;
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

fn hash_up_merkle_path<H: StarkHash + Send + Sync>(
    key: &BitSlice,
    mut current_hash: Felt,
    path_nodes: &[(ProofNode, u64)],
    skip_last: bool, // whether to skip the last element (e.g. if it has already been processed)
    trie: &mut MerkleTree<H>,
) -> Felt {
    let iter = path_nodes.iter().rev().skip(if skip_last { 1 } else { 0 });

    for (node, height) in iter {
        match node {
            ProofNode::Binary { left, right } => {
                let direction = Direction::from(key[*height as usize]);
                current_hash = match direction {
                    Direction::Left => {
                        let binary_node = hash_binary_node::<H>(current_hash, *right);
                        trie.insert_binary_node(*height, current_hash, *right, binary_node)
                            .unwrap();
                        binary_node
                    }
                    Direction::Right => {
                        let binary_node = hash_binary_node::<H>(*left, current_hash);
                        trie.insert_binary_node(*height, *left, current_hash, binary_node)
                            .unwrap();
                        binary_node
                    }
                };
            }
            ProofNode::Edge {
                path: edge_path,
                child: _,
            } => {
                let edge_node = hash_edge_node::<H>(edge_path, current_hash);
                trie.insert_edge_node(*height, edge_path, current_hash, edge_node)
                    .unwrap();
                current_hash = edge_node;
            }
        }
    }
    current_hash
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
        let mut partial_trie = PartialTrie::<Pedersen>::new(identifier1.into(), height);
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
        let mut partial_trie = PartialTrie::<Pedersen>::new(partial_trie_identifier.into(), 24);
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
        for i in 1..=10 {
            let mut key = vec![0; 3];
            key[0] = i;
            let value = Felt::from(i as u64 + 100);
            keys.push(BitVec::from_vec(key));
            values.push(value);
        }

        for (key, value) in keys.iter().zip(values.iter()).take(5) {
            bonsai_storage1.insert(&identifier, key, value).unwrap();
        }

        let id1 = id_builder.new_id();
        bonsai_storage1.commit(id1).unwrap();
        let mut current_root = bonsai_storage1.root_hash(&identifier).unwrap();

        let mut partial_trie = PartialTrie::<Pedersen>::new(identifier.clone().into(), 24);
        let mut next_roots = Vec::new();

        for (key, value) in keys.iter().zip(values.iter()).skip(5) {
            let tree1 = bonsai_storage1
                .tries
                .trees
                .entry(smallvec::smallvec![1])
                .or_insert_with(|| MerkleTree::new(identifier.clone().into(), 24));

            let proof_keys = vec![key];
            let proof = tree1
                .get_multi_proof(&bonsai_storage1.tries.db, proof_keys.iter())
                .unwrap();

            println!("--------------------------------");
            println!("REAL proof: {:?}", proof);
            println!("--------------------------------");

            //FOR DEBUGGING!
            let proof = partial_trie
                .trie
                .get_multi_proof(&bonsai_storage1.tries.db, proof_keys.iter())
                .unwrap();

            println!("--------------------------------");
            println!("PARTIAL proof: {:?}", proof);
            println!("--------------------------------");

            let next_root = partial_trie
                .next_root(
                    key,
                    *value,
                    current_root,
                    proof,
                    &mut bonsai_storage1.tries.db,
                )
                .unwrap();
            let proof = partial_trie
                .trie
                .get_multi_proof(&bonsai_storage1.tries.db, proof_keys.iter())
                .unwrap();

            next_roots.push(next_root);
            current_root = next_root;
        }

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

        let mut partial_trie = PartialTrie::<Pedersen>::new(identifier.clone().into(), height);
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
}
