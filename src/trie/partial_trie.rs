use super::iterator::PartialMerkleTreeTraverser;
use super::trie_db::TrieKeyType;
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
use crate::DBError;
use crate::ProofNode;
use crate::{databases::RocksDB, MultiProof};
use crate::{
    error::BonsaiStorageError, format, hash_map, id::Id, vec, BitSlice, BonsaiDatabase, ByteVec,
    EncodeExt, HashMap, HashSet, KeyValueDB, ToString, Vec,
};
use crate::{trie::merkle_node::NodeHandle, BitVec};
use core::marker::PhantomData;
use core::mem;
use parity_scale_codec::Decode;
use rocksdb::DB;
use starknet_types_core::{felt::Felt, hash::StarkHash};

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

#[derive(Debug)]
enum PartialTrieNodeOrFelt<'a> {
    Node(&'a PartialTrieNode),
    Felt(Felt),
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
                let node=
                    self.build_node_recursive(node_key, *height, key, value, &path_nodes, db)?;
                self.trie.proof_nodes[*node_key] = node;
                Ok(Felt::ZERO)
            }
            None => {
                log::trace!(
                    "Empty tree - this should never happen as we get proof from the full trie"
                );

                // Handle empty tree case
                let edge_node_hash = hash_edge_node::<H>(&Path(key.to_bitvec()), value);
                let edge_node = PartialTrieNode::Edge(EdgePartialTrieNode {
                    hash: Some(edge_node_hash),
                    path: Path(key.to_bitvec()),
                    height: 0,
                    child: ProofNodeHandle::Hash(value),
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
    ) -> Result<PartialTrieNode, BonsaiStorageError<DB::DatabaseError>> {
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

                let key_bytes = bitslice_to_bytes(key);
                if branch_height == key.len() {
                    edge.child = ProofNodeHandle::Hash(value);
                    self.trie
                        .cache_leaf_modified
                        .insert(key_bytes, InsertOrRemove::Insert(value));
                    return Ok(node);
                }

                let child_height = branch_height + 1;
                // Path from binary node to new leaf
                let new_path = key[child_height..].to_bitvec();
                // Path from binary node to existing child
                let old_path = edge.path[common.len() + 1..].to_bitvec();

                self.trie
                    .cache_leaf_modified
                    .insert(key_bytes, InsertOrRemove::Insert(value));

                let new_id= if new_path.is_empty() {
                    ProofNodeHandle::Hash(value)
                } else {
                    let edge_node = PartialTrieNode::Edge(EdgePartialTrieNode {
                        hash: None,
                        path: Path(new_path),
                        height: child_height as u64,
                        child: ProofNodeHandle::Hash(value),
                    });
                    let edge_id = self.trie.proof_nodes.insert(edge_node);

                    ProofNodeHandle::InMemory(edge_id)
                    
                };

                let old_id = if old_path.is_empty() {
                    edge.child
                } else {
                    let edge_node = PartialTrieNode::Edge(EdgePartialTrieNode {
                        hash: None,
                        path: Path(old_path),
                        height: child_height as u64,
                        child: edge.child,
                    });

                    let edge_id = self.trie.proof_nodes.insert(edge_node);
                    ProofNodeHandle::InMemory(edge_id)
                    
                };

                let new_direction = Direction::from(key[branch_height]);
                let (left_child, right_child) = match new_direction {
                    Direction::Left => (new_id, old_id),
                    Direction::Right => (old_id, new_id),
                };

                let branch = PartialTrieNode::Binary(BinaryPartialTrieNode {
                    hash: None,
                    height: branch_height as u64,
                    left: left_child,
                    right: right_child,
                });

                let new_node = if common.is_empty() {
                    branch
                } else {
                    let branch_node_key = self.trie.proof_nodes.insert(branch);

                    let new_node = PartialTrieNode::Edge(EdgePartialTrieNode {
                        hash: None,
                        path: Path(common.to_bitvec()),
                        height: edge.height,
                        child: ProofNodeHandle::InMemory(branch_node_key),
                    });
                    new_node
                };

                node = new_node;

                let key_bytes = bitslice_to_bytes(&key[..height as usize]);
                log::trace!("Adding to death row: {:?}", key_bytes);
                self.trie.death_row.insert(TrieKey::Trie(key_bytes));
                Ok(node)
            }
            PartialTrieNode::Binary(binary) => {
                log::trace!("BINARY: {:?}", binary);
                let child_height = binary.height + 1;
                let direction = Direction::from(key[binary.height as usize]);

                if child_height as usize == key.len() {
                    match direction {
                        Direction::Left => {
                            binary.left = ProofNodeHandle::Hash(value);
                        }
                        Direction::Right => {
                            binary.right = ProofNodeHandle::Hash(value);
                        }
                    };
                    let key_bytes = bitslice_to_bytes(key);
                    self.trie
                        .cache_leaf_modified
                        .insert(key_bytes, InsertOrRemove::Insert(value));

                    Ok(node)
                } else {
                    log::trace!("Binary node not at path end - should fetch full trie");
                    Err(PartialTrieError::NodeNotFound.into())
                }
            }
        }
    }

    fn get_node_or_felt<DB: BonsaiDatabase>(
        &self,
        node_handle: &ProofNodeHandle,
    ) -> Result<PartialTrieNodeOrFelt, BonsaiStorageError<DB::DatabaseError>> {
        let node_id = match node_handle {
            ProofNodeHandle::Hash(hash) => return Ok(PartialTrieNodeOrFelt::Felt(*hash)),
            ProofNodeHandle::InMemory(node_id) => *node_id,
        };
        let node = self
            .trie
            .proof_nodes
            .get(node_id)
            .ok_or(BonsaiStorageError::Trie(
                "Couldn't fetch node in the temporary storage".to_string(),
            ))?;
        Ok(PartialTrieNodeOrFelt::Node(node))
    }

    fn compute_root_hash<DB: BonsaiDatabase>(
        &self,
        hashes: &mut Vec<Felt>,
    ) -> Result<Felt, BonsaiStorageError<DB::DatabaseError>> {
        let handle = match &self.trie.root_node {
            Some(RootHandle::Loaded(node_id)) => *node_id,
            Some(RootHandle::Empty) => return Ok(Felt::ZERO),
            None => {
                return Err(BonsaiStorageError::Trie(
                    "Root node is not loaded".to_string(),
                ))
            }
        };
        let Some(node) = self.trie.proof_nodes.get(handle) else {
            return Err(BonsaiStorageError::Trie(
                "Could not fetch root node from storage".to_string(),
            ));
        };
        self.compute_hashes::<DB>(node, Path::default(), hashes)
    }

    /// Compute the hashes of all of the updated nodes in the merkle tree. This step
    /// is separate from [`commit_subtree`] as it is done in parallel using rayon.
    /// Computed hashes are pushed to the `hashes` vector, depth first.
    fn compute_hashes<DB: BonsaiDatabase>(
        &self,
        node: &PartialTrieNode,
        path: Path,
        hashes: &mut Vec<Felt>,
    ) -> Result<Felt, BonsaiStorageError<DB::DatabaseError>> {
        use PartialTrieNode::*;

        println!("Node to compute hashes: {:?}", node);
        match node {
            Binary(binary) => {
                // we check if we have one or two changed children

                let left_path = path.new_with_direction(Direction::Left);
                println!("Left path: {:?}", left_path);
                let node_left = self.get_node_or_felt::<DB>(&binary.left)?;
                println!("Node left: {:?}", node_left);
                let right_path = path.new_with_direction(Direction::Right);
                println!("Right path: {:?}", right_path);
                let node_right = self.get_node_or_felt::<DB>(&binary.right)?;
                println!("Node right: {:?}", node_right);

                let (left_hash, right_hash) = match (node_left, node_right) {
                    // #[cfg(feature = "std")]
                    (PartialTrieNodeOrFelt::Node(left), PartialTrieNodeOrFelt::Node(right)) => {
                        // two children: use rayon
                        let (left, right) = rayon::join(
                            || self.compute_hashes::<DB>(left, left_path, hashes),
                            || {
                                let mut hashes = vec![];
                                let felt =
                                    self.compute_hashes::<DB>(right, right_path, &mut hashes)?;
                                Ok::<_, BonsaiStorageError<DB::DatabaseError>>((felt, hashes))
                            },
                        );
                        let (left_hash, (right_hash, hashes2)) = (left?, right?);
                        hashes.extend(hashes2);
                        (left_hash, right_hash)
                    }
                    (left, right) => {
                        let left_hash = match left {
                            PartialTrieNodeOrFelt::Felt(felt) => felt,
                            PartialTrieNodeOrFelt::Node(node) => {
                                self.compute_hashes::<DB>(node, left_path, hashes)?
                            }
                        };
                        let right_hash = match right {
                            PartialTrieNodeOrFelt::Felt(felt) => felt,
                            PartialTrieNodeOrFelt::Node(node) => {
                                self.compute_hashes::<DB>(node, right_path, hashes)?
                            }
                        };
                        (left_hash, right_hash)
                    }
                };

                let hash = hash_binary_node::<H>(left_hash, right_hash);

                hashes.push(hash);
                Ok(hash)
            }

            Edge(edge) => {
                let mut child_path = path.clone();
                child_path.0.extend(&edge.path.0);
                let child_hash = match self.get_node_or_felt::<DB>(&edge.child)? {
                    PartialTrieNodeOrFelt::Felt(felt) => felt,
                    PartialTrieNodeOrFelt::Node(node) => {
                        self.compute_hashes::<DB>(node, child_path, hashes)?
                    }
                };

                let hash = hash_edge_node::<H>(&edge.path, child_hash);
                hashes.push(hash);

                Ok(hash)
            }
        }
    }

    /// Persists any changes in this subtree to storage.
    ///
    /// This necessitates recursively calculating the hash of, and
    /// in turn persisting, any changed child nodes. This is necessary
    /// as the parent node's hash relies on its children hashes.
    /// Hash computation is done in parallel with [`compute_hashes`] beforehand.
    ///
    /// In effect, the entire tree gets persisted.
    ///
    /// # Arguments
    ///
    /// * `node_handle` - The top node from the subtree to commit.
    /// * `hashes` - The precomputed hashes for the subtree as returned by [`compute_hashes`].
    ///   The order is depth first, left to right.
    ///
    /// # Panics
    ///
    /// Panics if the precomputed `hashes` do not match the length of the modified subtree.
    fn commit_subtree<DB: BonsaiDatabase>(
        &mut self,
        updates: &mut HashMap<TrieKey, InsertOrRemove<ByteVec>>,
        node_id: NodeKey,
        path: Path,
        hashes: &mut impl Iterator<Item = Felt>,
    ) -> Result<Felt, BonsaiStorageError<DB::DatabaseError>> {
        println!("Node id when committing: {:?}", node_id);
        match self
            .trie
            .proof_nodes
            .remove(node_id)
            .ok_or(BonsaiStorageError::Trie(
                "Couldn't fetch node in the temporary storage".to_string(),
            ))? {
            PartialTrieNode::Binary(mut binary) => {
                let left_path = path.new_with_direction(Direction::Left);
                let left_hash = match binary.left {
                    ProofNodeHandle::Hash(left_hash) => left_hash,
                    ProofNodeHandle::InMemory(node_id) => {
                        self.commit_subtree::<DB>(updates, node_id, left_path, hashes)?
                    }
                };
                let right_path = path.new_with_direction(Direction::Right);
                let right_hash = match binary.right {
                    ProofNodeHandle::Hash(right_hash) => right_hash,
                    ProofNodeHandle::InMemory(node_id) => {
                        self.commit_subtree::<DB>(updates, node_id, right_path, hashes)?
                    }
                };

                let hash = hashes.next().expect("mismatched hash state");
                // let hash = hash_binary_node::<H>(left_hash, right_hash);
                binary.hash = Some(hash);
                binary.left = ProofNodeHandle::Hash(left_hash);
                binary.right = ProofNodeHandle::Hash(right_hash);
                let key_bytes: ByteVec = path.into();
                updates.insert(
                    TrieKey::new(&self.trie.identifier, TrieKeyType::Trie, &key_bytes),
                    InsertOrRemove::Insert(PartialTrieNode::Binary(binary).encode_bytevec()),
                );
                Ok(hash)
            }
            PartialTrieNode::Edge(mut edge) => {
                let mut child_path = path.clone();
                child_path.0.extend(&edge.path.0);
                let child_hash = match edge.child {
                    ProofNodeHandle::Hash(right_hash) => right_hash,
                    ProofNodeHandle::InMemory(node_id) => {
                        self.commit_subtree::<DB>(updates, node_id, child_path, hashes)?
                    }
                };

                let hash = hashes.next().expect("mismatched hash state");
                edge.hash = Some(hash);
                // let hash = hash_edge_node::<H>(&edge.path, child_hash);
                edge.child = ProofNodeHandle::Hash(child_hash);
                let key_bytes: ByteVec = path.into();
                updates.insert(
                    TrieKey::new(&self.trie.identifier, TrieKeyType::Trie, &key_bytes),
                    InsertOrRemove::Insert(PartialTrieNode::Edge(edge).encode_bytevec()),
                );
                Ok(hash)
            }
        }
    }

    /// Calculate all the new hashes and the root hash.
    #[allow(clippy::type_complexity)]
    pub(crate) fn get_updates<DB: BonsaiDatabase>(
        &mut self,
    ) -> Result<
        impl Iterator<Item = (TrieKey, InsertOrRemove<ByteVec>)>,
        BonsaiStorageError<DB::DatabaseError>,
    > {
        let mut updates = HashMap::new();
        for node_key in mem::take(&mut self.trie.death_row) {
            updates.insert(node_key, InsertOrRemove::Remove);
        }

        if let Some(RootHandle::Loaded(node_id)) = &self.trie.root_node {
            // compute hashes
            let mut hashes = vec![];
            self.compute_root_hash::<DB>(&mut hashes)?;
            println!("Hashes: {:?}", hashes);
            // commit the tree
            self.commit_subtree::<DB>(
                &mut updates,
                *node_id,
                Path::default(),
                &mut hashes.into_iter(),
            )?;
        }

        self.trie.root_node = None; // unloaded

        for (key, value) in mem::take(&mut self.trie.cache_leaf_modified) {
            updates.insert(
                TrieKey::new(&self.trie.identifier, TrieKeyType::Flat, &key),
                match value {
                    InsertOrRemove::Insert(value) => InsertOrRemove::Insert(value.encode_bytevec()),
                    InsertOrRemove::Remove => InsertOrRemove::Remove,
                },
            );
        }
        // #[cfg(test)]
        // self.assert_empty(); // we should have visited the whole tree

        Ok(updates.into_iter())
    }

    /// # Panics
    ///
    /// Calling this function when the tree has uncommited changes is invalid as the hashes need to be recomputed.
    pub fn root_hash<DB: BonsaiDatabase, ID: Id>(
        &self,
        db: &KeyValueDB<DB, ID>,
    ) -> Result<Felt, BonsaiStorageError<DB::DatabaseError>> {
        match self.trie.root_node {
            Some(RootHandle::Empty) => Ok(Felt::ZERO),
            Some(RootHandle::Loaded(node_id)) => {
                let node = self.trie.proof_nodes.get(node_id).ok_or_else(|| {
                    BonsaiStorageError::Trie("Could not fetch root node from storage".into())
                })?;
                node.get_hash().ok_or_else(|| {
                    BonsaiStorageError::Trie("The tree has uncommited changes".into())
                })
            }
            None => {
                let Some(node) = Self::get_trie_branch_in_db_from_path(
                    &self.trie.death_row,
                    &self.trie.identifier,
                    db,
                    &Path::default(),
                )?
                else {
                    return Ok(Felt::ZERO);
                };
                Ok(node
                    .get_hash()
                    .expect("The fetched node has no computed hash"))
            }
        }
    }

    /// Get the node of the trie that corresponds to the path.
    fn get_trie_branch_in_db_from_path<DB: BonsaiDatabase, ID: Id>(
        death_row: &HashSet<TrieKey>,
        identifier: &[u8],
        db: &KeyValueDB<DB, ID>,
        path: &Path,
    ) -> Result<Option<PartialTrieNode>, BonsaiStorageError<DB::DatabaseError>> {
        log::trace!("getting: {:b}", path.0);

        let path: ByteVec = path.into();
        let key = TrieKey::new(identifier, TrieKeyType::Trie, &path);

        if death_row.contains(&key) {
            return Ok(None);
        }

        db.get(&key)?
            .map(|node| {
                log::trace!("got: {:?}", node);
                PartialTrieNode::decode(&mut node.as_slice()).map_err(|err| {
                    BonsaiStorageError::Trie(format!("Couldn't decode node: {}", err))
                })
            })
            .map_or(Ok(None), |r| r.map(Some))
    }

    // Commit a single merkle tree
    #[cfg(test)]
    pub(crate) fn commit<DB: BonsaiDatabase, ID: Id>(
        &mut self,
        db: &mut KeyValueDB<DB, ID>,
    ) -> Result<(), BonsaiStorageError<DB::DatabaseError>> {
        let db_changes = self.get_updates::<DB>()?;

        let mut batch = db.create_batch();
        for (key, value) in db_changes {
            match value {
                InsertOrRemove::Insert(value) => {
                    log::trace!("committing insert {:?} => {:?}", key, value);
                    db.insert(&key, &value, Some(&mut batch))?;
                }
                InsertOrRemove::Remove => {
                    log::trace!("committing remove {:?}", key);
                    db.remove(&key, Some(&mut batch))?;
                }
            }
        }
        db.write_batch(batch).unwrap();
        log::trace!("commit finished");

        Ok(())
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        databases::{create_rocks_db, RocksDB, RocksDBConfig},
        id::{BasicId, BasicIdBuilder},
        BonsaiStorage, BonsaiStorageConfig, MerkleTrees, PartialMerkleTrees,
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
        let mut fork_tree: BonsaiStorage<BasicId, RocksDB<'_, BasicId>, Pedersen, PartialMerkleTrees<Pedersen, RocksDB<'_, BasicId>, BasicId>> =
            BonsaiStorage::new_partial(
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

            fork_tree.insert_with_proof(&identifier4, key, value, proof, original_root).unwrap();
            fork_tree.commit(id_builder.new_id()).unwrap();
            let fork_hash = fork_tree.root_hash(&identifier4).unwrap();


            calculated_roots.push(fork_hash);
            current_root = fork_hash;
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

        fork_tree
        .insert_with_proof(
            &identifier4,
            one,
            &Felt::from(13),
            proof_for_one,
            original_root,
        )
        .unwrap();

        fork_tree.commit(id_builder.new_id()).unwrap();
        let calculated_updated_root = fork_tree.root_hash(&identifier4).unwrap();

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
        let mut forked_bonsai_storage: BonsaiStorage<BasicId, RocksDB<'_, BasicId>, Pedersen, PartialMerkleTrees<Pedersen, RocksDB<'_, BasicId>, BasicId>> =
            BonsaiStorage::new_partial(
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

            forked_bonsai_storage.insert_with_proof(&fork_identifier, key, value, proof, original_root).unwrap();
            forked_bonsai_storage.commit(id_builder.new_id()).unwrap();
            let fork_hash = forked_bonsai_storage.root_hash(&fork_identifier).unwrap();

            println!(
                "\nPartialTree NODES after adding new key-value pair: {:?}\n",
                partial_trie
                    .trie
                    .proof_nodes
                    .iter()
                    .map(|(k, v)| (k, v))
                    .collect::<HashMap<_, _>>()
            );

            calculated_roots.push(fork_hash);
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
            assert_eq!(expected_root, actual_root, "Expected root is not equal to actual root");
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

        let mut calculated_roots: Vec<Felt> = Vec::new();
        let mut i = 0;

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

        let mut current_root = original_root;

        for (key, value) in keys.iter().zip(values.iter()).skip(3) {
            i += 1;
            println!("ITERATION: {:?}", i);

            let proof_keys = vec![key];

            let proof = tree1
                .get_multi_proof(&base_tree.tries.db, proof_keys.iter())
                .unwrap();

            reference_tree.insert(&identifier3, key, value).unwrap();
            reference_tree.commit(id_builder.new_id()).unwrap();

            fork_tree.insert_with_proof(&identifier4, key, value, proof, original_root).unwrap();
            fork_tree.commit(id_builder.new_id()).unwrap();
            let fork_hash = fork_tree.root_hash(&identifier4).unwrap();

            calculated_roots.push(fork_hash);
            current_root = fork_hash;
        }

        for (key, value) in keys.iter().zip(values.iter()) {
            tree_to_compare.insert(&identifier2, key, value).unwrap();
        }

        tree_to_compare.commit(id_builder.new_id()).unwrap();
        let proof_keys = vec![keys.last().unwrap()];
        let proof = tree1
            .get_multi_proof(&tree_to_compare.tries.db, proof_keys.iter())
            .unwrap();

        let actual_root = tree_to_compare.root_hash(&identifier2).unwrap();
        assert_eq!(current_root, actual_root, "Next root calculation failed");

        fork_tree
            .insert_with_proof(
                &identifier4,
                one,
                &Felt::from(13),
                proof_for_one,
                original_root,
            )
            .unwrap();
        fork_tree.commit(id_builder.new_id()).unwrap();
        let calculated_updated_root = fork_tree.root_hash(&identifier4).unwrap();

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
