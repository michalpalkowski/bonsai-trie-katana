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
use crate::EncodeExt;
use crate::Id;
use crate::MultiProof;
use crate::ProofNode;
use crate::{trie::merkle_node::NodeHandle, BitSlice, BitVec};
use crate::{BonsaiDatabase, KeyValueDB};
use core::marker::PhantomData;
use hashbrown::HashMap;
use starknet_types_core::{felt::Felt, hash::StarkHash};
use std::collections::HashSet;
use std::mem;



        // CHCĘ przejść po wszystkich nodeach w proof od dołu do góry rekurencyjnie i dodać do PartialTrieStorage;
        // w kolejnych iteracjach sprawdzać czy w PartialTrieStorage jest node o takim hashu
        // jeśli jest to resztą proof się nie przejmujemy i możemy zdealokować go a obliczenia kontynuujemy używając hashy z PartialTrieStorage
        // jeśli nie to dodać do PartialTrieStorage node o takim hashu
        // hash każdego nodea chce wyliczać uzywajac funkcji hash_edge_node lub hash_binary_node w zależności od typu nodea
        // W przypadku nodea binary lewy/prawy hash określa path 




#[derive(Debug, thiserror::Error)]
pub enum PartialTrieError {
    #[error("Node not found in proof")]
    NodeNotFound,
}

/// Storage for caching nodes during partial trie operations
struct NodeCache {
    nodes: HashMap<Felt, ProofNode>,
}

impl NodeCache {
    fn new() -> Self {
        Self {
            nodes: HashMap::new(),
        }
    }

    fn get(&self, hash: &Felt) -> Option<&ProofNode> {
        self.nodes.get(hash)
    }

    fn insert(&mut self, hash: Felt, node: ProofNode) {
        self.nodes.insert(hash, node);
    }
}

/// Partial trie implementation that maintains a cache of nodes
pub struct PartialTrie<H: StarkHash> {
    trie: MerkleTree<H>,
    max_height: u8,
    original_root: Felt,
    node_keys: HashSet<NodeKey>,
    _hasher: PhantomData<H>,
}

impl<H: StarkHash + Send + Sync> PartialTrie<H> {
    pub fn new(identifier: ByteVec, max_height: u8, original_root: Felt) -> Self {
        Self {
            trie: MerkleTree::new(identifier, max_height),
            max_height,
            original_root,
            node_keys: HashSet::new(),
            _hasher: PhantomData,
        }
    }

    /// Calculate the next root hash after inserting a new value
    pub fn set<DB: BonsaiDatabase, ID: Id>(
        &mut self,
        key: &BitSlice,
        value: Felt,
        current_root: Felt,
        proof: MultiProof,
    ) -> Result<Felt, PartialTrieError> {
        let mut cache = NodeCache::new();
        let mut path = key.to_bitvec();
        
        // Process the proof recursively from bottom to top
        self.process_node(
            &mut cache,
            &proof,
            current_root,
            &mut path,
            value,
        )
    }

    /// Process a single node in the proof
    fn process_node(
        &mut self,
        cache: &mut NodeCache,
        proof: &MultiProof,
        node_hash: Felt,
        path: &mut BitVec,
        value: Felt,
    ) -> Result<Felt, PartialTrieError> {
        println!("Processing node with hash: {:?}", node_hash);
        println!("Current path: {:?}", path);
        println!("Current value: {:?}", value);

        // If we've reached the end of the path, return the value
        if path.is_empty() {
            println!("Reached end of path, returning value: {:?}", value);
            return Ok(value);
        }

        // Clone the node from cache if it exists to avoid borrowing issues
        let cached_node = cache.get(&node_hash).cloned();
        
        if let Some(node) = cached_node {
            println!("Found node in cache: {:?}", node);
            return self.process_cached_node(cache, &node, path, value);
        }

        // Get node from proof
        let node = proof.0.get(&node_hash).ok_or_else(|| {
            println!("Node not found in proof: {:?}", node_hash);
            println!("Available nodes in proof: {:?}", proof.0.keys().collect::<Vec<_>>());
            PartialTrieError::NodeNotFound
        })?;
        
        println!("Found node in proof: {:?}", node);
        
        // Store in cache
        cache.insert(node_hash, node.clone());

        // Process based on node type
        match node {
            ProofNode::Binary { left, right } => {
                let direction = Direction::from(path.pop().unwrap_or(false));
                let (next_hash, other_hash) = match direction {
                    Direction::Left => (*left, *right),
                    Direction::Right => (*right, *left),
                };

                println!("Binary node - direction: {:?}, next_hash: {:?}, other_hash: {:?}", 
                    direction, next_hash, other_hash);

                // Process the path we're following
                let new_hash = self.process_node(
                    cache,
                    proof,
                    next_hash,
                    path,
                    value,
                )?;

                // Create new binary node
                let binary_hash = match direction {
                    Direction::Left => hash_binary_node::<H>(new_hash, other_hash),
                    Direction::Right => hash_binary_node::<H>(other_hash, new_hash),
                };

                println!("Created new binary node with hash: {:?}", binary_hash);

                // Store new node in cache
                let new_node = ProofNode::Binary {
                    left: match direction {
                        Direction::Left => new_hash,
                        Direction::Right => other_hash,
                    },
                    right: match direction {
                        Direction::Left => other_hash,
                        Direction::Right => new_hash,
                    },
                };
                cache.insert(binary_hash, new_node);

                Ok(binary_hash)
            }
            ProofNode::Edge { child, path: edge_path } => {
                println!("Edge node - child: {:?}, path: {:?}", child, edge_path);

                // Find common path between edge_path and remaining path
                let common = common_path(edge_path, 0, path);
                let branch_height = common.len();

                // If we've reached the end of our path, we need to create a leaf
                if branch_height >= path.len() {
                    // Create a binary node at the split point
                    let binary_hash = hash_binary_node::<H>(value, *child);
                    
                    // Store new node in cache
                    let new_node = ProofNode::Binary {
                        left: value,
                        right: *child,
                    };
                    cache.insert(binary_hash, new_node);

                    // If we have a common prefix, create an edge node
                    if !common.is_empty() {
                        let edge_hash = hash_edge_node::<H>(&Path(common.to_bitvec()), binary_hash);
                        
                        // Store new node in cache
                        let new_node = ProofNode::Edge {
                            child: binary_hash,
                            path: Path(common.to_bitvec()),
                        };
                        cache.insert(edge_hash, new_node);
                        return Ok(edge_hash);
                    }

                    return Ok(binary_hash);
                }

                // If paths don't match at all, we need to create a binary node
                if common.is_empty() {
                    // Create a binary node at the current height
                    let binary_hash = hash_binary_node::<H>(value, *child);
                    
                    // Store new node in cache
                    let new_node = ProofNode::Binary {
                        left: value,
                        right: *child,
                    };
                    cache.insert(binary_hash, new_node);
                    return Ok(binary_hash);
                }

                // Remove the common path bits
                for _ in 0..common.len() {
                    path.pop();
                }

                // Process the remaining path
                let child_hash = self.process_node(
                    cache,
                    proof,
                    *child,
                    path,
                    value,
                )?;

                // Create new edge node with the common prefix
                let edge_hash = hash_edge_node::<H>(&Path(common.to_bitvec()), child_hash);
                
                println!("Created new edge node with hash: {:?}", edge_hash);

                // Store new node in cache
                let new_node = ProofNode::Edge {
                    child: child_hash,
                    path: Path(common.to_bitvec()),
                };
                cache.insert(edge_hash, new_node);

                Ok(edge_hash)
            }
        }
    }

    /// Process a node that was found in cache
    fn process_cached_node(
        &mut self,
        cache: &mut NodeCache,
        node: &ProofNode,
        path: &mut BitVec,
        value: Felt,
    ) -> Result<Felt, PartialTrieError> {
        println!("Processing cached node: {:?}", node);
        println!("Current path: {:?}", path);
        println!("Current value: {:?}", value);

        // If we've reached the end of the path, return the value
        if path.is_empty() {
            println!("Reached end of path in cached node, returning value: {:?}", value);
            return Ok(value);
        }

        match node {
            ProofNode::Binary { left, right } => {
                let direction = Direction::from(path.pop().unwrap_or(false));
                let (next_hash, other_hash) = match direction {
                    Direction::Left => (*left, *right),
                    Direction::Right => (*right, *left),
                };

                println!("Cached binary node - direction: {:?}, next_hash: {:?}, other_hash: {:?}", 
                    direction, next_hash, other_hash);

                // Process the path we're following
                let new_hash = self.process_node(
                    cache,
                    &MultiProof(HashMap::with_capacity(0)), // Empty proof since we're using cached nodes
                    next_hash,
                    path,
                    value,
                )?;

                // Create new binary node
                let binary_hash = match direction {
                    Direction::Left => hash_binary_node::<H>(new_hash, other_hash),
                    Direction::Right => hash_binary_node::<H>(other_hash, new_hash),
                };

                println!("Created new binary node from cache with hash: {:?}", binary_hash);

                // Store new node in cache
                let new_node = ProofNode::Binary {
                    left: match direction {
                        Direction::Left => new_hash,
                        Direction::Right => other_hash,
                    },
                    right: match direction {
                        Direction::Left => other_hash,
                        Direction::Right => new_hash,
                    },
                };
                cache.insert(binary_hash, new_node);

                Ok(binary_hash)
            }
            ProofNode::Edge { child, path: edge_path } => {
                println!("Cached edge node - child: {:?}, path: {:?}", child, edge_path);

                // Remove the path bits
                for _ in 0..edge_path.len() {
                    path.pop();
                }

                // Process child node
                let child_hash = self.process_node(
                    cache,
                    &MultiProof(HashMap::with_capacity(0)), // Empty proof since we're using cached nodes
                    *child,
                    path,
                    value,
                )?;

                // Create new edge node
                let edge_hash = hash_edge_node::<H>(edge_path, child_hash);
                
                println!("Created new edge node from cache with hash: {:?}", edge_hash);

                // Store new node in cache
                let new_node = ProofNode::Edge {
                    child: child_hash,
                    path: edge_path.clone(),
                };
                cache.insert(edge_hash, new_node);

                Ok(edge_hash)
            }
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
    use starknet_types_core::hash::Pedersen;

    #[test]
    fn test_set_single_case() {
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

        let mut id_builder = BasicIdBuilder::new();

        // Insert initial values
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

        // Test inserting a new value
        let mut new_key = vec![0; 3];
        new_key[0] = 5;
        let new_value = Felt::from(105);
        let new_key_bv = BitVec::from_vec(new_key.clone());

        let tree1 = bonsai_storage1
            .tries
            .trees
            .entry(smallvec::smallvec![1])
            .or_insert_with(|| MerkleTree::new(identifier.clone().into(), 24));

        // Get proof for the new key
        let proof_keys = vec![&new_key_bv];
        let proof = tree1
            .get_multi_proof(&bonsai_storage1.tries.db, proof_keys.iter())
            .unwrap();

        println!("Current root: {:?}", current_root);
        println!("Proof nodes: {:?}", proof.0);
        println!("New key: {:?}", new_key_bv);
        println!("New value: {:?}", new_value);

        let mut partial_trie = PartialTrie::<Pedersen>::new(identifier3.clone().into(), 24, current_root);
        let next_root = partial_trie
            .set::<RocksDB<BasicId>, BasicId>(
                &new_key_bv,
                new_value,
                current_root,
                proof,
            )
            .unwrap();

        // Verify the result
        bonsai_storage2
            .insert(&identifier2, &new_key_bv, &new_value)
            .unwrap();
        bonsai_storage2.commit(id_builder.new_id()).unwrap();

        let actual_root = bonsai_storage2.root_hash(&identifier2).unwrap();
        assert_eq!(next_root, actual_root, "Next root calculation failed");
    }

    #[test]
    fn test_new_next_root() {
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
        let _bonsai_storage3: BonsaiStorage<BasicId, RocksDB<'_, BasicId>, Pedersen> =
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
            PartialTrie::<Pedersen>::new(identifier3.into(), 24, current_root);
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
            println!("Current root: {:?}", current_root);
            println!("Proof nodes: {:?}", proof.0);
            println!("Key: {:?}", key);
            println!("Value: {:?}", value);

            let next_root = partial_trie
                .set::<RocksDB<BasicId>, BasicId>(
                    key,
                    *value,
                    current_root,
                    proof,
                )
                .unwrap();

            next_roots.push(next_root);
            current_root = next_root;
        }
        println!("---------Partial TRIE-----------");
        println!("{:?}\n", partial_trie.trie);

        for (key, value) in keys.iter().zip(values.iter()) {
            bonsai_storage2.insert(&identifier2, key, value).unwrap();
        }

        bonsai_storage2.commit(id_builder.new_id()).unwrap();

        let actual_root = bonsai_storage2.root_hash(&identifier2).unwrap();
        assert_eq!(current_root, actual_root, "Next root calculation failed");
    }
}
