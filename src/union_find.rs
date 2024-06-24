use std::{cell::Cell, iter::FusedIterator};

#[derive(Debug, Clone)]
pub struct UnionFind {
    cells: Vec<UnionFindCell>,
}

impl UnionFind {
    #[inline]
    pub const fn new() -> Self {
        Self { cells: Vec::new() }
    }

    #[inline]
    pub fn insert(&mut self) -> usize {
        let index = self.cells.len();
        self.cells.push(UnionFindCell {
            link: Cell::new(index as u32),
            size: 1,
            next: index as u32,
            prev: index as u32,
        });
        index
    }

    pub fn union(&mut self, a: usize, b: usize) -> usize {
        let a = self.find(a);
        let b = self.find(b);

        if a == b {
            return a;
        }

        // Decide which cell to use as the root.
        // We decide first by the priority and then by the size.
        let a_size = self.cells[a].size;
        let b_size = self.cells[b].size;
        let (root, child) = if a_size >= b_size { (a, b) } else { (b, a) };

        self.cells[root].size = a_size + b_size;
        self.cells[child].link.set(root as u32);

        // Connect the two cyclic doubly linked lists
        let root_prev = self.cells[root].prev;
        let child_prev = self.cells[child].prev;
        self.cells[root].prev = child_prev;
        self.cells[child].prev = root_prev;
        self.cells[root_prev as usize].next = child as u32;
        self.cells[child_prev as usize].next = root as u32;

        root
    }

    pub fn find(&self, mut index: usize) -> usize {
        // Perform path splitting to reduce the length of the chain of links.
        let mut cell = &self.cells[index].link;

        while cell.get() as usize != index {
            let parent_cell = &self.cells[cell.get() as usize].link;
            cell.set(parent_cell.get());
            index = cell.get() as usize;
            cell = parent_cell;
        }

        index
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.cells.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.cells.is_empty()
    }

    #[inline]
    pub fn class_size(&self, index: usize) -> u32 {
        let index = self.find(index);
        self.cells[index].size
    }

    #[inline]
    pub fn iter_class(&self, index: usize) -> ClassIter {
        let index = self.find(index);
        ClassIter {
            uf: self,
            remaining: self.cells[index].size as usize,
            current: index as u32,
        }
    }
}

#[derive(Debug, Clone)]
struct UnionFindCell {
    link: Cell<u32>,
    size: u32,
    next: u32,
    prev: u32,
}

pub struct ClassIter<'a> {
    uf: &'a UnionFind,
    remaining: usize,
    current: u32,
}

impl<'a> Iterator for ClassIter<'a> {
    type Item = usize;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.remaining = self.remaining.checked_sub(1)?;
        let current = self.current;
        self.current = self.uf.cells[current as usize].next;
        Some(current as usize)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }
}

impl<'a> ExactSizeIterator for ClassIter<'a> {
    #[inline]
    fn len(&self) -> usize {
        self.remaining
    }
}

impl<'a> FusedIterator for ClassIter<'a> {}
