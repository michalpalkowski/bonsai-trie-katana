use super::{
    merkle_node::{Direction, Node, NodeHandle},
    path::Path,
    tree::{MerkleTree, NodeKey, ProofNodeChildren, RootHandle},
};
use crate::{
    id::Id, key_value_db::KeyValueDB, trie::merkle_node::BinaryPartialTrieNode, BitSlice, BonsaiDatabase, BonsaiStorageError, MultiProof, ProofNode, Vec
};
use core::{fmt, marker::PhantomData};
use starknet_types_core::{felt::Felt, hash::StarkHash};
use std::collections::HashMap;
use crate::trie::merkle_node::PartialTrieNode;
use crate::trie::merkle_node::{ProofNodeHandle, EdgePartialTrieNode};

/// This trait's function will be called on every node visited during a seek operation.
pub trait NodeVisitor<H: StarkHash> {
    fn visit_node<DB: BonsaiDatabase>(
        &mut self,
        tree: &mut MerkleTree<H>,
        node_id: NodeKey,
        prev_height: usize,
    ) -> Result<(), BonsaiStorageError<DB::DatabaseError>>;
}

pub struct NoopVisitor<H>(PhantomData<H>);
impl<H: StarkHash> NodeVisitor<H> for NoopVisitor<H> {
    fn visit_node<DB: BonsaiDatabase>(
        &mut self,
        _tree: &mut MerkleTree<H>,
        _node_id: NodeKey,
        _prev_height: usize,
    ) -> Result<(), BonsaiStorageError<DB::DatabaseError>> {
        Ok(())
    }
}

pub trait PartialNodeVisitor<H: StarkHash> {
    fn visit_partial_node<DB: BonsaiDatabase>(
        &mut self,
        tree: &mut MerkleTree<H>,
        node_key: NodeKey,
        prev_height: usize,
    ) -> Result<(), BonsaiStorageError<DB::DatabaseError>>;
}

pub struct NoopPartialVisitor<H>(pub PhantomData<H>);
impl<H: StarkHash> PartialNodeVisitor<H> for NoopPartialVisitor<H> {
    fn visit_partial_node<DB: BonsaiDatabase>(
        &mut self,
        _tree: &mut MerkleTree<H>,
        _node_key: NodeKey,
        _prev_height: usize,
    ) -> Result<(), BonsaiStorageError<DB::DatabaseError>> {
        Ok(())
    }
}

pub struct MerkleTreeIterator<'a, H: StarkHash, DB: BonsaiDatabase, ID: Id> {
    pub(crate) tree: &'a mut MerkleTree<H>,
    pub(crate) db: &'a KeyValueDB<DB, ID>,
    /// Current iteration path.
    pub(crate) current_path: Path,
    /// The loaded nodes in the current path with their corresponding heights. Height is at the base of the node, meaning
    /// the first node here will always have height 0.
    pub(crate) current_nodes_heights: Vec<(NodeKey, usize)>,
    pub(crate) current_partial_nodes_heights: Vec<(NodeKey, usize)>,
    /// Current leaf hash. Note that partial traversal (traversal that stops midway through the tree) will
    /// also update this field if an exact match for the key is found, even though we may not have reached a leaf.
    pub(crate) leaf_hash: Option<Felt>,
    pub(crate) proof: Option<MultiProof>,
}

impl<'a, H: StarkHash, DB: BonsaiDatabase, ID: Id> fmt::Debug
    for MerkleTreeIterator<'a, H, DB, ID>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("MerkleTreeIterator")
            .field("cur_path", &self.current_path)
            .field("current_nodes_heights", &self.current_nodes_heights)
            .field("leaf_hash", &self.leaf_hash)
            .finish()
    }
}

impl<'a, H: StarkHash + Send + Sync, DB: BonsaiDatabase, ID: Id> MerkleTreeIterator<'a, H, DB, ID> {
    pub fn new(tree: &'a mut MerkleTree<H>, db: &'a KeyValueDB<DB, ID>) -> Self {
        Self {
            tree,
            db,
            current_path: Default::default(),
            current_nodes_heights: Vec::with_capacity(251),
            current_partial_nodes_heights: Vec::with_capacity(251),
            leaf_hash: None,
            proof: None,
        }
    }

    pub fn new_with_proof(
        tree: &'a mut MerkleTree<H>,
        db: &'a KeyValueDB<DB, ID>,
        proof: MultiProof,
    ) -> Self {
        Self {
            tree,
            db,
            current_path: Default::default(),
            current_nodes_heights: Vec::with_capacity(251),
            current_partial_nodes_heights: Vec::with_capacity(251),
            leaf_hash: None,
            proof: Some(proof),
        }
    }

    #[cfg(test)]
    /// For testing purposes.
    pub fn cur_nodes_ids(&self) -> Vec<u64> {
        use slotmap::Key;
        self.current_nodes_heights
            .iter()
            .map(|n| n.0.data().as_ffi() & !(1 << 32))
            .collect::<Vec<_>>()
    }

    pub fn seek_to(&mut self, key: &BitSlice) -> Result<(), BonsaiStorageError<DB::DatabaseError>> {
        self.traverse_to(&mut NoopVisitor(PhantomData), key)
    }

    fn traverse_one(
        &mut self,
        node_id: NodeKey,
        height: usize,
        key: &BitSlice,
    ) -> Result<Option<NodeKey>, BonsaiStorageError<DB::DatabaseError>> {
        self.current_nodes_heights
            .push((node_id, self.current_path.len()));

        let node = self.tree.get_node_mut::<DB>(node_id)?;
        let (node_handle, path_matches) = match node {
            Node::Binary(binary_node) => {
                log::trace!(
                    "Continue from binary node current_path={:?} key={:b}",
                    self.current_path,
                    key,
                );
                let next_direction = Direction::from(key[self.current_path.len()]);
                self.current_path.push(bool::from(next_direction));
                (binary_node.get_child(next_direction), true)
            }
            Node::Edge(edge_node) => {
                self.current_path.extend_from_bitslice(&edge_node.path);
                (edge_node.child, edge_node.path_matches(key, height))
            }
        };

        // path_matches is false when the edge node doesn't match the path we want to preload so we return nothing.
        log::trace!(
            "Compare: path_matches={path_matches} {:?} ?= {:b} (node_handle {node_handle:?})",
            self.current_path,
            key
        );
        if !path_matches || self.current_path.len() >= key.len() {
            self.leaf_hash = if path_matches && self.current_path.len() == key.len() {
                node_handle.as_hash()
            } else {
                None
            };
            return Ok(None); // end of traversal
        }

        let child_key = self
            .tree
            .load_node_handle(self.db, node_handle, &self.current_path)?;

        // update parent ref
        match self.tree.get_node_mut::<DB>(node_id)? {
            Node::Binary(binary_node) => {
                *binary_node.get_child_mut(Direction::from(
                    *self
                        .current_path
                        .last()
                        .expect("current path should have a length > 0 at this point"),
                )) = NodeHandle::InMemory(child_key);
            }
            Node::Edge(edge_node) => {
                edge_node.child = NodeHandle::InMemory(child_key);
            }
        };

        Ok(Some(child_key))
    }

    pub fn traverse_to<V: NodeVisitor<H>>(
        &mut self,
        visitor: &mut V,
        key: &BitSlice,
    ) -> Result<(), BonsaiStorageError<DB::DatabaseError>> {
        // First, truncate the curent path and nodes list to match the new key.
        log::trace!("Start traverse_to");

        if key.is_empty() {
            self.current_nodes_heights.clear();
            self.current_path.clear();
            self.leaf_hash = None;
            return Ok(());
        }

        let shared_prefix_len = self
            .current_path
            .iter()
            .zip(key)
            .take_while(|(a, b)| *a == *b)
            .count();

        let nodes_new_len = if shared_prefix_len == 0 {
            0
        } else {
            // partition point is a binary search under the hood
            // TODO(perf): measure whether binary search is actually better than reverse iteration - the happy path may be that
            //  only the last few bits are different.
            self.current_nodes_heights
                .partition_point(|(_node, height)| *height < shared_prefix_len)
        };
        log::trace!(
            "Truncate pre node id cache shared_prefix_len={:?}, nodes_new_len={:?}, cur_path_nodes_heights={:?}, current_path={:?}",
            shared_prefix_len, nodes_new_len,
            self.current_nodes_heights,
            self.current_path,
        );

        self.current_nodes_heights.truncate(nodes_new_len);
        self.current_path.truncate(key.len());

        let mut next_to_visit = if let Some((node_id, height)) = self.current_nodes_heights.pop() {
            self.current_path.truncate(height);
            visitor.visit_node::<DB>(self.tree, node_id, height)?;
            self.traverse_one(node_id, height, key)?
        } else {
            // Start from tree root.
            self.current_path.clear();
            let Some(node_id) = self.tree.load_root_node(self.db)? else {
                // empty tree, not found
                self.leaf_hash = None;
                return Ok(());
            };
            visitor.visit_node::<DB>(self.tree, node_id, 0)?;
            Some(node_id)
        };

        log::trace!(
            "Starting traversal with path {:?}, next={:?}",
            self.current_path,
            next_to_visit
        );

        // Tree traversal :)
        loop {
            log::trace!("Loop start cur={:?} key={:b}", self.current_path, key);

            let Some(node_id) = next_to_visit else {
                return Ok(());
            };

            next_to_visit = self.traverse_one(node_id, self.current_path.len(), key)?;
            if let Some(next_id) = next_to_visit {
                visitor.visit_node::<DB>(self.tree, next_id, self.current_path.len())?;
            }

            log::trace!(
                "Got nodeid={:?} height={}, cur path={:?}, next to visit={:?}",
                node_id,
                self.current_path.len(),
                self.current_path,
                next_to_visit
            );
        }
    }

    fn traverse_one_partial(
        &mut self,
        node_id: NodeKey,
        height: usize,
        key: &BitSlice,
    ) -> Result<Option<NodeKey>, BonsaiStorageError<DB::DatabaseError>> {
        self.current_partial_nodes_heights
            .push((node_id, self.current_path.len()));
        println!("Current path: {:?}", self.current_path);
        println!("Current path len: {:?}", self.current_path.len());
        println!("Key: {:?}", key);
        let current_path_len = self.current_path.len();
        let current_path_len_at_beginning = self.current_path.len().clone();

        let partial_trie_node= self.tree.get_proof_node_mut::<DB>(node_id)?;
        // let path_matches = partial_trie_node.path_matches(key, height);

        let (proof_node_child,proof_node_handle, path_matches) = match partial_trie_node {
            PartialTrieNode::Binary(binary_node) => {
                log::trace!(
                    "Continue from binary node current_path={:?} key={:b}",
                    self.current_path,
                    key,
                );
                let next_direction = Direction::from(key[self.current_path.len()]);
                self.current_path.push(bool::from(next_direction));
                (binary_node.get_child(next_direction), binary_node.get_child_handle(next_direction), true)
            }
            PartialTrieNode::Edge(edge_node) => {
                self.current_path.extend_from_bitslice(&edge_node.path);
                (edge_node.child, edge_node.child_handle, edge_node.path_matches(key, height))
            }
        };

        //I need to add here condition for path mathes probably
        if !path_matches || self.current_path.len() >= key.len() {
            println!("Child: {:?}", proof_node_handle.as_hash());
            self.leaf_hash = if path_matches && self.current_path.len() == key.len() {
               proof_node_handle.as_hash()
            } else {
                None
            };
            println!("Leaf hash: {:?}", self.leaf_hash);
            return Ok(None); // end of traversal
        }

        println!("Proof node handle: {:?}", proof_node_handle);
        let next_node_id = self.tree.load_proof_node_handle::<DB, ID>(self.db, proof_node_handle, &self.current_path)?;
        println!("Next node id: {:?}", next_node_id);
        if let Some(existing_node_id) = next_node_id {
            // I THINK THIS MIGHT BE THE BUG BECAUSE WE HAVE NONE ON A LEAF HERE
            // SO WE WILL TRY TO GET THE REST OF THE NODES IN ELSE STATEMENT FROM FULL PROOF WHILE BEING ON A LEAF WHICH IS BAD
            println!("Existing node id: {:?}", existing_node_id);
            Ok(Some(existing_node_id))
        } else {
            println!("NODE DID NOT EXIST IN OUR PARTIAL TRIE LETS GET IT FROM FULL PROOF");
            //HERE IS THE POINT WHERE WE NEED TO GET THE REST OF THE NODES FROM FULL PROOF
            // WE WILL BE HERE IN FIRST ITERATION BECAUSE WE HAVE EMPTY TRIE
            let proof_clone = self.proof.clone().unwrap().0.clone();

            // its a child of the last node in partial trie and it does not exist in partial trie
            //so it wasn't changed so we can just get it from proof
            let Some(child_node) = proof_clone.get(&proof_node_child.as_hash().unwrap()) else {
                println!("DID NOT FIND THE NODE IN PROOF");
                // WE SHOULD BE HERE ON FIRST ITERATION WHEN WE GET TO THE LEAF
                self.leaf_hash = None;
                return Ok(None);
            };
            println!("FOUND THE NODE IN PROOF");
            println!(
                "New child node to update parent reference: {:?}",
                child_node
            );
            // Create new node with correct type of children

            let child = match child_node {
                ProofNode::Binary { left, right } => {
                    PartialTrieNode::Binary(BinaryPartialTrieNode {
                        left: ProofNodeHandle::Hash(*left),
                        right: ProofNodeHandle::Hash(*right),
                        left_handle: ProofNodeHandle::Hash(Felt::ZERO), //Felt::Zero means None
                        right_handle: ProofNodeHandle::Hash(Felt::ZERO), //Felt::Zero means None
                    })
                }
                ProofNode::Edge { child, path } => {
                    PartialTrieNode::Edge(EdgePartialTrieNode {
                        child: ProofNodeHandle::Hash(*child),
                        path: path.clone(),
                        child_handle: ProofNodeHandle::Hash(Felt::ZERO), //Felt::Zero means None
                    })
                }
            };

            let new_node_id = self
                .tree
                .proof_nodes
                .insert(child);

            // Update children reference in parent node
          
            match self.tree.get_proof_node_mut::<DB>(node_id)? {
                PartialTrieNode::Binary(binary_node) => {
                    *binary_node.get_child_handle_mut(Direction::from(
                        *self
                            .current_path
                            .last()
                            .expect("current path should have a length > 0 at this point"),
                    )) = ProofNodeHandle::InMemory(new_node_id);
                }
                PartialTrieNode::Edge(edge_node) => {
                    edge_node.child = ProofNodeHandle::InMemory(new_node_id);
                }
            };

            Ok(Some(new_node_id))
        }
    }

    pub fn traverse_to_partial<V: PartialNodeVisitor<H>>(
        &mut self,
        visitor: &mut V,
        key: &BitSlice,
        root: Felt,
    ) -> Result<(), BonsaiStorageError<DB::DatabaseError>> {
        if key.is_empty() {
            self.current_partial_nodes_heights.clear();
            self.current_path.clear();
            self.leaf_hash = None;
            return Ok(());
        }
        let shared_prefix_len = self
            .current_path
            .iter()
            .zip(key)
            .take_while(|(a, b)| *a == *b)
            .count();

        let nodes_new_len = if shared_prefix_len == 0 {
            0
        } else {
            self.current_partial_nodes_heights
                .partition_point(|(_node, height)| *height < shared_prefix_len)
        };

        self.current_partial_nodes_heights.truncate(nodes_new_len);
        self.current_path.truncate(key.len());

        let mut next_to_visit =
            if let Some((node_id, height)) = self.current_partial_nodes_heights.pop() {
                self.current_path.truncate(height);
                // visitor.visit_partial_node::<DB>(self.tree, node_id, height)?;
                self.traverse_one_partial(node_id, height, key)?
            } else {
                // If we have already consstructed partial trie then we have node key for current root
                //But its only one try because it should be updated
                if let Some(root_node_id) = self.tree.current_root_node_id {
                    // visitor.visit_partial_node::<DB>(self.tree, root_node_id, 0)?;
                    Some(root_node_id)
                } else {
                    // Start from tree root.
                    self.current_path.clear();

                    // Get root hash from proof
                    let proof_clone = self.proof.clone().unwrap().0.clone();
                    println!("Proof nodes: {:?}", proof_clone);

                    // Get root node from proof by its hash
                    let Some(root_node) = proof_clone.get(&root) else {
                        println!("No root node in proof");
                        self.leaf_hash = None;
                        return Ok(());
                    };
                    println!("Found root node in proof: {:?}", root_node);

                    // Children are set recursively in traverse_one_partial
                    let partial_root_node = match root_node {
                        ProofNode::Binary { left, right } => {
                            PartialTrieNode::Binary(BinaryPartialTrieNode {
                                left: ProofNodeHandle::Hash(*left),
                                right: ProofNodeHandle::Hash(*right),
                                left_handle: ProofNodeHandle::Hash(Felt::ZERO), //Felt::Zero means None
                                right_handle: ProofNodeHandle::Hash(Felt::ZERO), //Felt::Zero means None
                            })
                        }
                        ProofNode::Edge { child, path } => {
                            PartialTrieNode::Edge(EdgePartialTrieNode {
                                child: ProofNodeHandle::Hash(*child),
                                path: path.clone(),
                                child_handle: ProofNodeHandle::Hash(Felt::ZERO), //Felt::Zero means None
                            })
                        }
                    };
        
                    let root_node_id = self
                        .tree
                        .proof_nodes
                        .insert(partial_root_node);

                    println!("Created root node in tree: {:?}", root_node_id);
                    self.tree.current_root_node_id = Some(root_node_id);

                    Some(root_node_id)
                }
            };

        log::trace!(
            "Starting traversal with path {:?}, next={:?}",
            self.current_path,
            next_to_visit
        );

        // Tree traversal :)
        loop {
            log::trace!("Loop start cur={:?} key={:b}", self.current_path, key);

            let Some(node_id) = next_to_visit else {
                return Ok(());
            };

            next_to_visit = self.traverse_one_partial(node_id, self.current_path.len(), key)?;

            // if let Some(next_id) = next_to_visit {
            //     visitor.visit_partial_node::<DB>(self.tree, next_id, self.current_path.len())?;
            // }

            log::trace!(
                "Got nodeid={:?} height={}, cur path={:?}, next to visit={:?}",
                node_id,
                self.current_path.len(),
                self.current_path,
                next_to_visit
            );
        }
    }
}
#[cfg(test)]
mod tests {
    //! The tree used in this series of tests looks like this:
    //! ```
    //!                    │                   
    //!                   ┌▼┐                  
    //!                (1)│ │[0]               
    //!                   │ │                  
    //!                   └┬┘                  
    //!                (7)┌▼┐                  
    //!              ┌────┴─┴────────┐         
    //!             ┌▼┐             ┌▼┐        
    //!          (6)│ │[0100]    (5)│ │[000000]
    //!             │ │             │ │        
    //!             └┬┘             │ │        
    //!          (4)┌▼┐             │ │        
    //!        ┌────┴─┴─────┐       │ │        
    //!        │           ┌▼┐      │ │        
    //!    (2)┌▼┐       (3)│ │[0]   │ │        
    //!    ┌──┴─┴─┐        │ │      │ │        
    //!    │      │        └┬┘      └┬┘        
    //!   0x1    0x2       0x3      0x4        
    //! ```

    use crate::id::BasicIdBuilder;
    use crate::{
        databases::{create_rocks_db, RocksDB, RocksDBConfig},
        id::{BasicId, Id},
        trie::iterator::MerkleTreeIterator,
        BonsaiDatabase, BonsaiStorage, BonsaiStorageConfig,
    };
    use crate::{BitVec, HashMap};
    use bitvec::{bits, order::Msb0};
    use prop::{collection::vec, sample::size_range};
    use proptest::prelude::*;
    use starknet_types_core::{
        felt::Felt,
        hash::{Pedersen, StarkHash},
    };

    const ONE: Felt = Felt::ONE;
    const TWO: Felt = Felt::TWO;
    const THREE: Felt = Felt::THREE;
    const FOUR: Felt = Felt::from_hex_unchecked("0x4");
    const FIVE: Felt = Felt::from_hex_unchecked("0x5");
    const SIX: Felt = Felt::from_hex_unchecked("0x6");

    #[test]
    fn test_iterator_seek_to() {
        test_iterator_seek_to_inner((0..all_cases_len()).collect());
    }
    fn test_iterator_seek_to_inner(cases: Vec<usize>) {
        let _ = env_logger::builder().is_test(true).try_init();
        log::set_max_level(log::LevelFilter::Trace);
        let tempdir = tempfile::tempdir().unwrap();
        let db = create_rocks_db(tempdir.path()).unwrap();
        let mut bonsai_storage: BonsaiStorage<BasicId, _, Pedersen> = BonsaiStorage::new(
            RocksDB::<BasicId>::new(&db, RocksDBConfig::default()),
            BonsaiStorageConfig::default(),
            8,
        );

        bonsai_storage
            .insert(&[], bits![u8, Msb0; 1,0,0,0,0,0,0,0], &ONE)
            .unwrap();
        bonsai_storage
            .insert(&[], bits![u8, Msb0; 0,1,0,0,0,0,0,0], &TWO)
            .unwrap();
        bonsai_storage
            .insert(&[], bits![u8, Msb0; 1,1,0,0,0,0,0,0], &THREE)
            .unwrap();
        bonsai_storage
            .insert(&[], bits![u8, Msb0; 0,0,1,0,0,0,0,0], &FOUR)
            .unwrap();
        bonsai_storage
            .insert(&[], bits![u8, Msb0; 1,0,1,0,0,0,0,0], &FIVE)
            .unwrap();
        // bonsai_storage
        //     .insert(&[], bits![u8, Msb0; 0,0,0,0,0,1,1,0], &SIX)
        //     .unwrap();

        let mut id_builder = BasicIdBuilder::new();
        let id1 = id_builder.new_id();
        // bonsai_storage.commit(id1).unwrap();
        let mut bv = BitVec::new();
        bv.extend_from_bitslice(&bits![u8, Msb0; 1,0,0,0,0,0,0,0]);
        let proof_keys: Vec<BitVec> = vec![bv];
        let multi_proof = bonsai_storage.get_multi_proof(&[], &proof_keys);
        println!("\nMulti proof for node 0x1: {:?}\n", multi_proof.unwrap());

        let mut bv = BitVec::new();
        bv.extend_from_bitslice(&bits![u8, Msb0; 0,1,0,0,0,0,0,0]);
        let proof_keys: Vec<BitVec> = vec![bv];
        let multi_proof = bonsai_storage.get_multi_proof(&[], &proof_keys);
        println!("\nMulti proof for node 0x2: {:?}\n", multi_proof.unwrap());

        let mut bv = BitVec::new();
        bv.extend_from_bitslice(&bits![u8, Msb0; 1,1,0,0,0,0,0,0]);
        let proof_keys: Vec<BitVec> = vec![bv];
        let multi_proof = bonsai_storage.get_multi_proof(&[], &proof_keys);
        println!("\nMulti proof for node 0x3: {:?}\n", multi_proof.unwrap());

        let mut bv = BitVec::new();
        bv.extend_from_bitslice(&bits![u8, Msb0; 0,0,1,0,0,0,0,0]);
        let proof_keys: Vec<BitVec> = vec![bv];
        let multi_proof = bonsai_storage.get_multi_proof(&[], &proof_keys);
        println!("\nMulti proof for node 0x4: {:?}\n", multi_proof.unwrap());

        let mut bv = BitVec::new();
        bv.extend_from_bitslice(&bits![u8, Msb0; 1,0,1,0,0,0,0,0]);
        let proof_keys: Vec<BitVec> = vec![bv];
        let multi_proof = bonsai_storage.get_multi_proof(&[], &proof_keys);
        println!("\nMulti proof for node 0x5: {:?}\n", multi_proof.unwrap());

        bonsai_storage.dump();

        // Trie
        println!("\ntree: {:?}\n", bonsai_storage.tries.trees);

        let tree = bonsai_storage
            .tries
            .trees
            .get_mut(&smallvec::smallvec![])
            .unwrap();
        println!(
            "\nTree NODES: {:?}\n",
            tree.nodes
                .iter()
                .map(|(k, v)| (k, v))
                .collect::<HashMap<_, _>>()
        );

        let mut iter = MerkleTreeIterator::new(tree, &bonsai_storage.tries.db);

        let cases_funcs = all_cases();
        for case in cases {
            cases_funcs[case](&mut iter)
        }
    }

    #[allow(clippy::type_complexity)]
    fn all_cases<H: StarkHash + Send + Sync, DB: BonsaiDatabase, ID: Id>(
    ) -> Vec<fn(&mut MerkleTreeIterator<H, DB, ID>)> {
        vec![
            // SEEK TO LEAF
            // case 0
            |iter| {
                // from scratch, should find the leaf
                iter.seek_to(bits![u8, Msb0; 0,0,0,1,0,0,0,0]).unwrap();
                assert_eq!(iter.leaf_hash, Some(ONE));
                assert_eq!(iter.cur_nodes_ids(), vec![1, 7, 6, 4, 2]);
                println!("{iter:?}");
            },
            // case 1
            |iter| {
                // from a closeby leaf, should backtrack and find the next one
                iter.seek_to(bits![u8, Msb0; 0,0,0,1,0,0,0,1]).unwrap();
                assert_eq!(iter.leaf_hash, Some(TWO));
                assert_eq!(iter.cur_nodes_ids(), vec![1, 7, 6, 4, 2]);
                println!("{iter:?}");
            },
            // case 2
            |iter| {
                // backtrack farther, should find the leaf
                iter.seek_to(bits![u8, Msb0; 0,0,0,1,0,0,1,0]).unwrap();
                assert_eq!(iter.leaf_hash, Some(THREE));
                assert_eq!(iter.cur_nodes_ids(), vec![1, 7, 6, 4, 3]);
                println!("{iter:?}");
            },
            // case 3
            |iter| {
                // backtrack farther, should find the leaf
                iter.seek_to(bits![u8, Msb0; 0,1,0,0,0,0,0,0]).unwrap();
                assert_eq!(iter.leaf_hash, Some(FOUR));
                assert_eq!(iter.cur_nodes_ids(), vec![1, 7, 5]);
                println!("{iter:?}");
            },
            // case 4
            |iter| {
                // similar case
                iter.seek_to(bits![u8, Msb0; 0,0,0,1,0,0,0,1]).unwrap();
                assert_eq!(iter.leaf_hash, Some(TWO));
                assert_eq!(iter.cur_nodes_ids(), vec![1, 7, 6, 4, 2]);
                println!("{iter:?}");
            },
            // SEEK MIDWAY INTO THE TREE
            // case 5
            |iter| {
                // jump midway into an edge
                iter.seek_to(bits![u8, Msb0; 0,1,0,0,0]).unwrap();
                // The current path should reflect the tip of the edge
                assert_eq!(iter.current_path.0, bits![u8, Msb0; 0,1,0,0,0,0,0,0]);
                assert_eq!(iter.leaf_hash, None);
                assert_eq!(iter.cur_nodes_ids(), vec![1, 7, 5]);
                println!("{iter:?}");
            },
            // case 6
            |iter| {
                // jump midway into an edge, but its child is not a leaf
                iter.seek_to(bits![u8, Msb0; 0,0,0]).unwrap();
                // The current path should reflect the edge
                assert_eq!(iter.current_path.0, bits![u8, Msb0; 0,0,0,1,0,0]);
                assert_eq!(iter.leaf_hash, None);
                assert_eq!(iter.cur_nodes_ids(), vec![1, 7, 6]);
                println!("{iter:?}");
            },
            // case 7
            |iter| {
                // jump to a binary node
                iter.seek_to(bits![u8, Msb0; 0,0,0,1,0,0,0]).unwrap();
                assert_eq!(iter.current_path.0, bits![u8, Msb0; 0,0,0,1,0,0,0]);
                assert_eq!(iter.leaf_hash, None);
                assert_eq!(iter.cur_nodes_ids(), vec![1, 7, 6, 4]);
                println!("{iter:?}");
            },
            // case 8
            |iter| {
                // jump to the end of an edge
                iter.seek_to(bits![u8, Msb0; 0,0,0,1,0,0]).unwrap();
                // The current path should reflect the tip of the edge
                assert_eq!(iter.current_path.0, bits![u8, Msb0; 0,0,0,1,0,0]);
                assert_eq!(iter.leaf_hash, None);
                assert_eq!(iter.cur_nodes_ids(), vec![1, 7, 6]);
                println!("{iter:?}");
            },
            // case 9
            |iter| {
                // jump to top
                iter.seek_to(bits![u8, Msb0; ]).unwrap();
                assert_eq!(iter.leaf_hash, None);
                assert_eq!(iter.current_path.0, bits![u8, Msb0; ]);
                assert_eq!(iter.cur_nodes_ids(), vec![]);
                println!("{iter:?}");
            },
            // case 10
            |iter| {
                // jump to first node
                iter.seek_to(bits![u8, Msb0; 0]).unwrap();
                assert_eq!(iter.current_path.0, bits![u8, Msb0; 0]);
                assert_eq!(iter.leaf_hash, None);
                assert_eq!(iter.cur_nodes_ids(), vec![1]);
                println!("{iter:?}");
            },
            // case 11
            |iter| {
                // jump to non existent node, returning same edge
                iter.seek_to(bits![u8, Msb0; 0,1,0,1,0,0,0]).unwrap();
                assert_eq!(iter.current_path.0, bits![u8, Msb0; 0,1,0,0,0,0,0,0]);
                assert_eq!(iter.leaf_hash, None);
                assert_eq!(iter.cur_nodes_ids(), vec![1, 7, 5]);
                println!("{iter:?}");
            },
            // case 12
            |iter| {
                // jump to non existent node, deviating from edge, should not go into the children
                iter.seek_to(bits![u8, Msb0; 1,0,0,1,0,0,0]).unwrap();
                assert_eq!(iter.current_path.0, bits![u8, Msb0; 0]);
                assert_eq!(iter.leaf_hash, None);
                assert_eq!(iter.cur_nodes_ids(), vec![1]);
                println!("{iter:?}");
            },
            // case 13
            |iter| {
                // jump to non existent node, deviating from first node
                iter.seek_to(bits![u8, Msb0; 1]).unwrap();
                assert_eq!(iter.current_path.0, bits![u8, Msb0; 0]);
                assert_eq!(iter.leaf_hash, None);
                assert_eq!(iter.cur_nodes_ids(), vec![1]);
                println!("{iter:?}");
            },
        ]
    }

    fn all_cases_len() -> usize {
        all_cases::<Pedersen, RocksDB<'static, BasicId>, BasicId>().len()
    }

    proptest::proptest! {
        // #![proptest_config(ProptestConfig::with_cases(5))] // comment this when developing, this is mostly for faster ci & whole workspace `cargo test`
        #[test]
        /// This proptest will apply the above seek_to cases in a random order, and possibly with duplicates.
        fn proptest_seek_to(cases in vec(0..all_cases_len(), size_range(0..20)).boxed()) {
            test_iterator_seek_to_inner(cases)
        }
    }
}
