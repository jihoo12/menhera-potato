//! Bump arena for kernel nodes (terms, values, levels, environments).

use std::fmt;
use std::marker::PhantomData;

/// Typed stable index into an arena slice.
///
/// Manual impls avoid phantom `T: Copy/Eq` bounds from derives.
pub struct Idx<T> {
    raw: u32,
    _tag: PhantomData<fn() -> T>,
}

impl<T> Clone for Idx<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for Idx<T> {}

impl<T> PartialEq for Idx<T> {
    fn eq(&self, other: &Self) -> bool {
        self.raw == other.raw
    }
}

impl<T> Eq for Idx<T> {}

impl<T> std::hash::Hash for Idx<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.raw.hash(state);
    }
}

impl<T> Idx<T> {
    #[inline]
    pub fn from_raw(raw: u32) -> Self {
        Self {
            raw,
            _tag: PhantomData,
        }
    }

    #[inline]
    pub fn raw(self) -> u32 {
        self.raw
    }

    #[inline]
    pub fn as_usize(self) -> usize {
        self.raw as usize
    }
}

impl<T> fmt::Debug for Idx<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Idx({})", self.raw)
    }
}

/// Bump arena: append-only storage with typed indices.
#[derive(Debug, Default)]
pub struct Arena<T> {
    nodes: Vec<T>,
}

impl<T> Arena<T> {
    pub fn new() -> Self {
        Self { nodes: Vec::new() }
    }

    pub fn with_capacity(cap: usize) -> Self {
        Self {
            nodes: Vec::with_capacity(cap),
        }
    }

    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    pub fn alloc(&mut self, node: T) -> Idx<T> {
        let raw = self.nodes.len() as u32;
        self.nodes.push(node);
        Idx::from_raw(raw)
    }

    pub fn get(&self, idx: Idx<T>) -> &T {
        &self.nodes[idx.as_usize()]
    }

    pub fn get_mut(&mut self, idx: Idx<T>) -> &mut T {
        &mut self.nodes[idx.as_usize()]
    }

    /// Reset to empty, keeping allocated capacity.
    pub fn clear(&mut self) {
        self.nodes.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn alloc_and_get() {
        let mut arena = Arena::new();
        let a = arena.alloc(10u32);
        let b = arena.alloc(20u32);
        assert_eq!(*arena.get(a), 10);
        assert_eq!(*arena.get(b), 20);
        assert_eq!(arena.len(), 2);
        arena.clear();
        assert!(arena.is_empty());
    }
}
