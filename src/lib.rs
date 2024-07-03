//! Libra is a library for building constraint based type inference engines.
//! See the [book] for more details on the scope and usage.
//!
//! [book]: https://zrho.github.io/libra-types/book/
use std::{iter::FusedIterator, ops::Range};

mod mycroft;
pub mod recipes;
mod type_set;
mod union_find;
pub mod util;

pub use mycroft::run_mycroft;
pub use type_set::{ParentsIter, SolveError, State, TypeSet, UnifyError};

/// A row cons cell that represents an entry in a row.
#[derive(Debug, Clone, Copy)]
pub struct RowCons<L> {
    /// The label for this entry in the row.
    pub label: L,
    /// The type that is associated to this entry in the row.
    pub value: TypeIndex,
    /// The remainder of the row.
    pub rest: TypeIndex,
}

/// Representation of a type within Libra's type language.
///
/// To avoid unnecessary traversals and allocations when converting between
/// Libra's types and the types of the programming language, nested types
/// are represented via their [`TypeIndex`]s again. Recursive calls to
/// [`TypeSet::get_type`] may be used to extract a complete representation
/// of the type.
#[derive(Debug, Clone, Copy)]
pub enum Type<L> {
    /// A type constructor that is applied to a sequence of arguments.
    /// Types of this form unify when the names of the type constructors match
    /// and the arguments pairwise unify with each other.
    Ctr(L, Children),
    /// A type variable.
    Var(TypeIndex),
    /// An empty row.
    RowEmpty,
    /// A row cons cell. See [`RowCons`] for more detail.
    RowCons(RowCons<L>),
    /// An inconsistent type.
    /// This is used whenever the type inference engine attempts to unify
    /// incompatible types, detects a cyclic type or otherwise determines a type
    /// to be ill-formed.
    Error,
}

macro_rules! make_index {
    (
        $(#[$meta:meta])*
        $vis:vis struct $name:ident;
    ) => {
        $(#[$meta])*
        #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
        $vis struct $name(::std::num::NonZeroU32);

        impl ::std::fmt::Debug for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                f.debug_tuple(stringify!($name)).field(&self.index()).finish()
            }
        }

        impl $name {
            #[inline]
            pub const fn new(index: usize) -> Self {
                assert!(index < u32::MAX as usize);
                Self(unsafe { ::std::num::NonZeroU32::new_unchecked(index as u32 + 1) })
            }

            #[inline]
            pub const fn index(&self) -> usize {
                (self.0.get() - 1) as usize
            }
        }
    };
}

make_index! {
    /// An index that identifies a type in a [`TypeSet`].
    pub struct TypeIndex;
}

/// List of children of a type in a [`TypeSet`].
///
/// Since the indices of a type's children are consecutive, this list can
/// be represented efficiently.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Children {
    pub(crate) index: TypeIndex,
    pub(crate) len: u16,
}

impl Children {
    pub fn get(&self, index: usize) -> TypeIndex {
        if index > self.len as usize {
            panic!(
                "index {} out of bounds in children list of length {}",
                index, self.len
            );
        }

        TypeIndex::new(self.index.index() + 1 + index as usize)
    }

    /// Returns the number of child types in this list.
    #[inline]
    pub fn len(&self) -> usize {
        self.len as usize
    }

    /// Returns `true` when the list contains no child types.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Returns an iterator over all child types in this list.
    #[inline]
    pub fn iter(&self) -> ChildrenIter {
        self.into_iter()
    }
}

impl IntoIterator for Children {
    type Item = TypeIndex;
    type IntoIter = ChildrenIter;

    fn into_iter(self) -> Self::IntoIter {
        let start = self.index.index() + 1;
        let end = start + self.len as usize;
        ChildrenIter(start..end)
    }
}

/// Iterator returned by [`Children::iter`].
#[derive(Clone)]
pub struct ChildrenIter(Range<usize>);

impl Iterator for ChildrenIter {
    type Item = TypeIndex;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(TypeIndex::new)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl ExactSizeIterator for ChildrenIter {
    fn len(&self) -> usize {
        self.0.len()
    }
}

impl FusedIterator for ChildrenIter {}
