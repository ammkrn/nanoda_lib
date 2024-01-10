//! A union find data structure for caching definitional equalities
use crate::util::{new_fx_index_map, FxIndexMap};
use std::hash::Hash;

#[derive(Debug)]
pub(crate) struct UnionFind<A>
where
    A: PartialEq + Eq + Hash, {
    node_map: FxIndexMap<A, UFNode>,
}

// Because we have `IndexMap`, we can get away with `UFNode` only containing parent and rank.
#[derive(Debug, Clone)]
struct UFNode {
    parent: usize,
    rank: usize,
}

impl<A> UnionFind<A>
where
    A: PartialEq + Eq + Hash,
{
    pub(crate) fn new() -> Self { UnionFind { node_map: new_fx_index_map() } }

    pub(crate) fn clear(&mut self) { self.node_map.clear() }

    /// If `e` is in the UF data structure already, return
    /// the index it's located at.
    ///
    /// If `e` was not already in the UF data structure,
    /// insert it with a new UFNode and return the index at which
    /// it's located.
    fn get_or_push(&mut self, e: A) -> usize {
        if let Some(idx) = self.node_map.get_index_of(&e) {
            idx
        } else {
            let this_idx = self.node_map.len();
            let new_node = UFNode { parent: this_idx, rank: 0 };
            let (idx, was_new) = self.node_map.insert_full(e, new_node);
            debug_assert_eq!(this_idx, idx);
            debug_assert!(was_new.is_none());
            idx
        }
    }

    /// For an element (a : A) that occupies index `idx`, find and return the root
    /// element of its UF/equivalence class, while also setting this element's parent
    /// to be the root parent (path compression).
    fn find_parent_idx(&mut self, idx: usize) -> usize {
        // Recursively get the parent's parent's parent, etc. until we find the root,
        // which is the element for which `parent_idx == idx`
        let parent_idx = self.node_map.get_index(idx).map(|(_, node)| node.parent).unwrap();
        if parent_idx == idx {
            idx
        } else {
            // compression
            // recurse to find the parent's parent's parent, etc. until we reach the root.
            let root = self.find_parent_idx(parent_idx);
            // Set this element's parent to the now-known root element
            // for this union class.
            match self.node_map.get_index_mut(idx) {
                None => panic!(),
                // Now that we know what the root is, do path compression by setting
                // this element's parent to the root.
                Some((_, ufnode)) => {
                    ufnode.parent = root;
                }
            }
            root
        }
    }

    /// For two root elements that were not previously members of the same equivalence class,
    /// merge them into the same equivalence class by marking either `x_root.parent = y_root`
    /// or vice-versa, while managing `rank` for efficiency.
    fn link_roots(&mut self, x_root: usize, y_root: usize) {
        // This is only called after `find_parent_idx`, so `x` and `y` are the indices
        // of the root elements of their respective equivalence classes. If `x_root` and `y_root`
        // are the same, we don't need to do anything since (1) they're the same already, and (2)
        // `find_parent_idx` performs path compression.
        if x_root != y_root {
            // At this point we know that `x_root` and `y_root` were not yet marked as equivalent/
            // members of the same equivalence class.
            let x_root_rank = self.node_map.get_index(x_root).map(|(_, node)| node.rank).unwrap();
            let y_root_rank = self.node_map.get_index(y_root).map(|(_, node)| node.rank).unwrap();
            if y_root_rank < x_root_rank {
                // if x_root and y_root were not previously marked as equivalent, and y_root has
                // a lower rank, union the equivalence classes by setting y_root's parent to x_root.
                match self.node_map.get_index_mut(y_root) {
                    None => panic!(),
                    Some((_, ufnode)) => {
                        ufnode.parent = x_root;
                    }
                }
            } else {
                // if x_root and y_root were not previously marked as equivalent, and x_root has
                // a lower or equal rank, union the equivalence classes by setting x_root's parent to y_root.
                match self.node_map.get_index_mut(x_root) {
                    None => panic!(),
                    Some((_, ufnode)) => {
                        ufnode.parent = y_root;
                    }
                }
            }
            // If they happen to have the same rank, increment y_root's rank by one.
            if x_root_rank == y_root_rank {
                match self.node_map.get_index_mut(y_root) {
                    None => panic!(),
                    Some((_, ufnode)) => {
                        ufnode.rank += 1;
                    }
                }
            }
        }
    }

    /// update the union-find structure so that `a` and `b` are members of the same
    /// equivalence class, and perform path compression.
    pub(crate) fn union(&mut self, a: A, b: A) {
        let (a, b) = (self.get_or_push(a), self.get_or_push(b));
        let (a_root, b_root) = (self.find_parent_idx(a), self.find_parent_idx(b));
        self.link_roots(a_root, b_root);
    }

    /// Check whether e1 and e2 are known to be equal.
    pub(crate) fn check_uf_eq(&mut self, e1: A, e2: A) -> bool {
        let (e1, e2) = (self.get_or_push(e1), self.get_or_push(e2));
        self.find_parent_idx(e1) == self.find_parent_idx(e2)
    }
}
