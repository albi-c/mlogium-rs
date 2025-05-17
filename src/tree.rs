use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::hash::Hash;
use parse::span::Span;

#[derive(Debug, Clone)]
pub struct TreeNode<K: Hash + Eq, V> {
    value: V,
    tree: Tree<K, V>,
    span: Span,
}

impl<K: Hash + Eq, V> TreeNode<K, V> {
    pub fn value(&self) -> &V {
        &self.value
    }
    pub fn value_mut(&mut self) -> &mut V {
        &mut self.value
    }

    pub fn tree(&self) -> &Tree<K, V> {
        &self.tree
    }
    pub fn tree_mut(&mut self) -> &mut Tree<K, V> {
        &mut self.tree
    }

    pub fn span(&self) -> Span {
        self.span.clone()
    }
}

#[derive(Debug, Clone)]
pub struct Tree<K: Hash + Eq, V> {
    data: HashMap<K, TreeNode<K, V>>,
}

impl<K: Hash + Eq, V> Default for Tree<K, V> {
    fn default() -> Self {
        Self {
            data: HashMap::new(),
        }
    }
}

impl<K: Hash + Eq, V> Tree<K, V> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn insert(&mut self, span: Span, key: K, value: V) -> Result<&mut TreeNode<K, V>, Span> {
        match self.data.entry(key) {
            Entry::Occupied(e) => {
                Err(e.get().span())
            },
            Entry::Vacant(e) => {
                Ok(e.insert(TreeNode {
                    value,
                    tree: Tree::new(),
                    span,
                }))
            },
        }
    }

    pub fn get(&self, key: &K) -> Option<&TreeNode<K, V>> {
        self.data.get(key)
    }
}
