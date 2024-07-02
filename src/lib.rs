//! Libra is a library for building constraint based type inference engines.
//! For an overview of the type language, see [`Type`].
//!
//! # Constraint Based Type Inference
//!
//! The intended usage of Libra is to infer or check the types of a program
//! in three stages:
//!
//!  1. **Constraint Generation:** We traverse the input program and generate
//!     types and type constraints in a [`TypeSet`] that together describe the type inference
//!     problem associated to the program. During this process we keep track of
//!     the association between locations in the program and the [`TypeIndex`]s
//!     in the [`TypeSet`] that should correspond to the type of that program location.
//!  2. **Constraint Solving:** Once all types and constraints are collected in the
//!     [`TypeSet`], we solve the type constraints. The [`TypeSet`] keeps track of
//!     constraints that remain unsolved. For any such constraint, a user provided
//!     procedure uses unification to incorporate the knowledge encoded in the
//!     constraint into the [`TypeSet`]. The procedure can then decide whether to
//!     consider the constraint solved, to signal an error or to postpone solving
//!     the constraint to when more information becomes known.
//!     Postponed constraints are reawakened when one of their referenced types changes.
//!  3. **Elaboration:** After all constraints are solved, we extract the type information
//!     from the [`TypeSet`] to generate a program representation with type annotations.
//!     This step uses the association between [`TypeIndex`]s and program locations that
//!     has been recorded in the constraint generation step.
//!
//! The names of type constructors and of row labels are drawn from a
//! user-specified type `L` that must implement [`Copy`] and [`Eq`].
//! This is intended to be used together with
//! [string interning](https://en.wikipedia.org/wiki/String_interning).
//!
//! # The Type System
//!
//! ## Polymorphism
//!
//! We believe that [let should not be generalised](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/tldi10-vytiniotis.pdf).
//! Classical Hindley Milner type systems perform type generalisation at local
//! let bindings. Unfortunately this system is incompatible with a general
//! and extensible constraint system. We therefore do not implement support
//! for local implicit generalisation in libra. That design choice also paves
//! the way for potential future support of [local assumptions](https://simon.peytonjones.org/outsideinx/).
//!
//! ## Rows
//!
//! Libra supports a form of row types with
//! [scoped labels](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/scopedlabels.pdf).
//! Rows can be used to model (extensible) record types and variant types.
//! A row is a sequence of row cons cells, specifying a label, a type and the
//! rest of the row.
//! Depending on the type that the row ends in, we classify rows as follows:
//!
//!  - **Closed Row:** The sequence ends in an empty row.
//!  - **Open Row:** The sequence ends in a row variable.
//!  - **Improper Row:** The sequence ends in a type that is not a row.
//!
//! Entries with different labels can be exchanged freely, while the order
//! of entries with the same label must be preserved.
//! This avoids label conflicts when using row polymorphism.
//! In cases where duplicate labels are not desired, this can be enforced
//! by using custom constraints.
//! We currently do not support rows with
//! [first class labels](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/fclabels.pdf)
//! directly, but this feature can be (partly) simulated using constraints as well.
//!
//! # Type Errors
//!
//! A type inference engine should not only work when the program is well-typed,
//! but also allow for diagnostics in case of a type error.
//! Producing helpful diagnostics is a difficult and underspecified problem.
//! Classical implementations of Hindley Milner type inference stop at the first
//! type error that is encountered, which due to the non-local nature of unification
//! may also be far from the location of the actual mistake in the code.
//!
//! Libra is designed to be used with the
//! [Mycroft](https://dl.acm.org/doi/abs/10.1145/3022671.2983994)
//! approach to error reporting.
//! When Libra encounters an error, it can produce an *unsatisfiable core*, i.e.
//! a subset of the type constraints which can not be simultaneously satisfied.
//! The unsatisfiable core can then be used to selectively disable individual
//! constraints until a (close to) minimal set of constraints is found without
//! which the type inference problem is satisfiable.
//! These error constraints can then be used to produce the appropriate error messages.
//! This approach for error reporting was chosen since it can produce decent
//! quality type errors, does not stop at the first error but reports multiple
//! errors, and allows for extensibility in the constraint language.
//!
//! In the case of an error, Mycroft runs the type inference engine many times.
//! Depending on the size of the program and the complexity of the custom
//! constraint language, this process may be slow.
//! For situations where high quality error messages are not necessary,
//! the repeated resolving may be skipped and the ill-typed program rejected
//! immediately.
//!
//! # Usage Examples
//!
//! This library is deliberately kept small, favouring composable abstractions
//! that can be used as the foundation for a variety of type system features.
//! As a consequence, it might not be immediately obvious how some common high
//! level features map into libra types. Below we list some examples.
//!
//! ## Kinds
//! ## Algebraic Data Types
//! ## Type Classes
//! ## Type Families as Constraints
//! ## Data Kinds and Primitives
//! ## Type Level Lists
//! ## Skolem Variables
//!
//! # Performance
//!
//! Type inference should be fast. It can appear as part of a language server
//! and therefore impact the editing experience of a programmer. It is part of
//! a build process and should not dramatically slow down the compilation of
//! large programs. Ideally type inference and ideally type checking should
//! be fast enough that there is no temptation to omit it.
//!
//! Cloning a TypeSet is O(n). This is not entirely ideal since the Mycroft
//! error reporting scheme needs a clone for every iteration, including the
//! first one for the happy case in which no type errors occur. So far we
//! haven’t found a way to avoid this without a performance penalty in practice.
//! Instead we ensure that cloning a TypeSet amounts to a small and constant
//! number of heap allocations and calls to memcpy.
use fxhash::FxHashSet;
use std::{iter::FusedIterator, ops::Range};
use thiserror::Error;
use util::{extract_rec, DebugType};

mod union_find;
use union_find::{ClassIter, UnionFind};

pub mod util;

/// A set of types and type constraints.
///
/// Types and constraints are represented uniformly.
#[derive(Debug, Clone)]
pub struct TypeSet<L> {
    uf: UnionFind,
    types: Vec<TypeData<L>>,
    errors: Vec<TypeIndex>,
    active: Vec<TypeIndex>,
}

impl<L> TypeSet<L>
where
    L: Eq + Copy,
{
    /// Creates a new empty [`TypeSet`].
    pub fn new() -> Self {
        Self {
            uf: UnionFind::new(),
            types: Vec::new(),
            errors: Vec::new(),
            active: Vec::new(),
        }
    }

    /// Insert a type constructor with the given number of type arguments.
    ///
    /// A fresh type variable is generated for every type argument.
    /// To set an argument to a specific type, this type variable can be unified
    /// with the other type by using [`TypeSet::unify`]. This is guaranteed to
    /// succeed for the first time that the variable is unified.
    ///
    /// # Example
    ///
    /// ```
    /// # use libra_types::TypeSet;
    /// let mut types = TypeSet::<u32>::new();
    ///
    /// const TYPE_INT: u32 = 0;
    /// const TYPE_ARRAY: u32 = 1;
    ///
    /// let (int, _) = types.insert_ctr(TYPE_INT, 0);
    /// let (array, array_children) = types.insert_ctr(TYPE_ARRAY, 1);
    ///
    /// types.unify(array_children.get(0), int).unwrap();
    /// ```
    pub fn insert_ctr(&mut self, label: L, args: usize) -> (TypeIndex, Children) {
        let index = self.insert_slot(TypeSlot::Ctr(label, args as u16), State::Inert);

        for i in 0..args {
            self.insert_slot(TypeSlot::Arg(i as u16), State::Inert);
        }

        let children = Children {
            index,
            len: args as u16,
        };

        (index, children)
    }

    /// Insert a type constraint with the given number of type arguments.
    ///
    /// This method works analogously to [`TypeSet::insert_ctr`], except that
    /// it additionally marks the inserted type constructor as an active constraint.
    /// In particular the index of the newly inserted constraint will be returned
    /// by [`TypeSet::pop_active`] at some point so that the constraint can be discharged.
    pub fn insert_con(&mut self, label: L, args: usize) -> (TypeIndex, Children) {
        let (index, children) = self.insert_ctr(label, args);
        self.types[index.index()].state = State::Active;
        (index, children)
    }

    /// Insert an empty row.
    #[inline]
    pub fn insert_row_empty(&mut self) -> TypeIndex {
        self.insert_slot(TypeSlot::RowEmpty, State::Inert)
    }

    /// Insert a new row cons cell.
    ///
    /// Fresh type variables are generated for the value and rest type of the
    /// row cons cell. To set either of these to a specific type, the type
    /// variable can be unified with that type by using [`TypeSet::unify`].
    /// This is guaranteed to succeed for the first time that the variable is unified.
    pub fn insert_row_cons(&mut self, label: L) -> (TypeIndex, RowCons<L>) {
        let index = self.insert_slot(TypeSlot::RowCons(label), State::Inert);
        let value = self.insert_slot(TypeSlot::Arg(0), State::Inert);
        let rest = self.insert_slot(TypeSlot::Arg(1), State::Inert);
        (index, RowCons { label, value, rest })
    }

    /// Insert a type variable.
    #[inline]
    pub fn insert_var(&mut self) -> TypeIndex {
        self.insert_slot(TypeSlot::Var, State::Inert)
    }

    #[inline]
    fn insert_slot(&mut self, slot: TypeSlot<L>, state: State) -> TypeIndex {
        let index = TypeIndex::new(self.uf.insert());

        self.types.push(TypeData {
            canonical: index,
            slot,
            state,
        });

        index
    }

    /// Returns the type at a given index.
    ///
    /// To avoid unneccessary allocation and traversal, the type representation
    /// that is returned by this method is shallow. Nested types are again
    /// represented by their index, which can be inspected by subsequent calls
    /// to this method.
    ///
    /// # Panics
    ///
    /// When the type index is not part of this type set.    
    #[inline]
    pub fn get(&self, index: TypeIndex) -> Type<L> {
        self.get_type_internal(self.canonical(index))
    }

    /// Returns a debug representation of the type at a given index.
    ///
    /// # Panics
    ///
    /// When the type index is not part of this type set.    
    #[inline]
    pub fn get_debug(&self, index: TypeIndex) -> DebugType<L>
    where
        L: Ord,
    {
        extract_rec(&self, |l| l, index)
    }

    /// Returns the representative of a [`TypeIndex`]s equivalence class.
    ///
    /// # Panics
    ///
    /// When the type index is not part of this type set.
    #[inline]
    pub fn canonical(&self, index: TypeIndex) -> TypeIndex {
        self.types[self.uf.find(index.index())].canonical
    }

    /// Attempts to unify two types.
    ///
    /// In the case that a type mismatch or a cycle is detected, the offending
    /// type is marked as involved in an error via [`TypeSet::record_error`]
    /// and the type set consequently becomes inconsistent. At that point
    /// the [`TypeSet::unsat_core`] method can be used to extract an unsatisfiable
    /// core.
    ///
    /// # Panics
    ///
    /// When the type index is not part of this type set.
    pub fn unify(&mut self, a: TypeIndex, b: TypeIndex) -> Result<(), SolveError> {
        // Unify the two types if they aren't already in the same equivalence class
        let a = self.canonical(a);
        let b = self.canonical(b);

        if a == b {
            return Ok(());
        }

        let root = TypeIndex::new(self.uf.union(a.index(), b.index()));

        let a_prio = self.types[a.index()].slot.priority();
        let b_prio = self.types[b.index()].slot.priority();

        if a_prio >= b_prio {
            self.types[root.index()].canonical = a;
        } else {
            self.types[root.index()].canonical = b;
        }

        // Check if we created a cycle and mark the ancestors as dirty
        self.unify_check_cycle(a)?;

        // Match the types and recursively unify if necessary
        match (self.get_type_internal(a), self.get_type_internal(b)) {
            (Type::Error, _) => a,
            (_, Type::Error) => b,

            (Type::Ctr(a_label, a_args), Type::Ctr(b_label, b_args)) => {
                if a_label != b_label {
                    self.record_error(a);
                    return Err(SolveError::new(a));
                }

                if a_args.len() != b_args.len() {
                    self.record_error(a);
                    return Err(SolveError::new(a));
                }

                for (a_arg, b_arg) in a_args.iter().zip(b_args) {
                    // TODO: Error context?
                    self.unify(a_arg, b_arg)?;
                }

                root
            }

            (Type::RowEmpty, Type::RowEmpty) => root,

            (Type::RowCons(a_row), Type::RowCons(b_row)) => {
                self.unify_rows(a_row, b_row)?;
                root
            }

            (Type::Var(_), _) => b,
            (_, Type::Var(_)) => a,

            _ => {
                self.record_error(a);
                return Err(SolveError::new(a));
            }
        };

        Ok(())
    }

    fn unify_check_cycle(&mut self, start: TypeIndex) -> Result<(), SolveError> {
        // TODO: Reuse these allocations?
        let mut stack: Vec<_> = self.parents(start).collect();
        let mut visited = FxHashSet::default();

        while let Some(index) = stack.pop() {
            if !visited.insert(index) {
                continue;
            }

            if index == start {
                self.record_error(start);
                return Err(SolveError::new(start));
            }

            if let State::Deferred = self.state(index) {
                self.types[index.index()].state = State::Active;
                self.active.push(index);
            }

            stack.extend(self.parents(index));
        }

        Ok(())
    }

    fn unify_rows(&mut self, a: RowCons<L>, b: RowCons<L>) -> Result<(), SolveError> {
        // TODO: This creates a lot of subrows.
        // We can avoid this but that requires some allocation.
        if a.label == b.label {
            self.unify(a.value, b.value)?;
            self.unify(a.rest, b.rest)?;
        } else {
            let (r, r_cons) = self.insert_row_cons(b.label);
            let (s, s_cons) = self.insert_row_cons(a.label);
            self.unify(r_cons.rest, s_cons.rest)?;
            self.unify(r_cons.value, b.value)?;
            self.unify(s_cons.value, a.value)?;
            self.unify(r, a.rest)?;
            self.unify(s, b.rest)?;
        }

        Ok(())
    }

    /// Mark a type as involved in a type error.
    ///
    /// # Panics
    ///
    /// When the type index is not part of this type set.    
    pub fn record_error(&mut self, index: TypeIndex) {
        let error = TypeIndex::new(self.uf.insert());
        self.errors.push(error);

        self.types.push(TypeData {
            canonical: error,
            slot: TypeSlot::Error,
            state: State::Inert,
        });

        let repr = self.uf.union(index.index(), error.index());
        self.types[repr].canonical = error;
    }

    #[inline]
    fn get_type_internal(&self, index: TypeIndex) -> Type<L> {
        match self.types[index.index()].slot {
            TypeSlot::Ctr(label, len) => Type::Ctr(label, Children { index, len }),
            TypeSlot::Arg(_) => Type::Var(index),
            TypeSlot::Var => Type::Var(index),
            TypeSlot::Error => Type::Error,
            TypeSlot::RowEmpty => Type::RowEmpty,
            TypeSlot::RowCons(label) => Type::RowCons(RowCons {
                label,
                value: TypeIndex::new(index.index() + 1),
                rest: TypeIndex::new(index.index() + 2),
            }),
        }
    }

    /// Returns an iterator over the parents of a type.
    ///
    /// # Panics
    ///
    /// When the type index is not part of this type set.    
    #[inline]
    pub fn parents(&self, index: TypeIndex) -> ParentsIter<L> {
        ParentsIter {
            types: self,
            inner: self.uf.iter_class(index.index()),
        }
    }

    /// Returns whether the type set is consistent, i.e. no error has been encountered yet.
    #[inline]
    pub fn is_consistent(&self) -> bool {
        self.errors.is_empty()
    }

    /// Returns the set of constraints which directly or indirectly could have contributed
    /// to the errors that have been encountered. Returns an empty set when the type set
    /// is consistent.
    pub fn unsat_core(&self) -> FxHashSet<TypeIndex> {
        let mut visited = FxHashSet::default();
        let mut stack = Vec::new();
        let mut unsat_core = FxHashSet::default();

        stack.extend(self.errors.iter().copied());

        while let Some(index) = stack.pop() {
            if !visited.insert(index) {
                continue;
            }

            stack.extend(self.parents(index));

            if let Type::Ctr(_, cs) = self.get(index) {
                if let State::Active | State::Solved = self.types[index.index()].state {
                    unsat_core.insert(index);
                    stack.extend(cs);
                }
            }
        }

        unsat_core
    }

    pub fn mark_solved(&mut self, index: TypeIndex) {
        if let State::Active = self.types[index.index()].state {
            self.types[index.index()].state = State::Solved;
        }
    }

    pub fn mark_removed(&mut self, index: TypeIndex) {
        self.types[index.index()].state = State::Removed;
    }

    #[inline]
    pub fn state(&self, index: TypeIndex) -> State {
        self.types[index.index()].state
    }

    /// Removes a constraint from the stack of *active* constraints.
    ///
    /// The constraint will transition into the deferred state.
    /// Unless consequently marked as solved or removed, the constraint
    /// will become active again when itself or one of its descendents
    /// are updated via unification.
    pub fn pop_active(&mut self) -> Option<(TypeIndex, L, Children)> {
        while let Some(index) = self.active.pop() {
            if index != self.canonical(index) {
                continue;
            }

            assert_eq!(self.types[index.index()].state, State::Active);
            self.types[index.index()].state = State::Deferred;

            let Type::Ctr(label, cs) = self.get(index) else {
                panic!("invariant: a constraint must have been a type constructor");
            };

            return Some((index, label, cs));
        }

        None
    }
}

/// The state of a type or type constraint in a [`TypeSet`] during type inference.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum State {
    /// The type is a constraint to be solved. It will at some point be returned
    /// via [`TypeSet::pop_active`] by the type set that contains it.
    Active,
    /// The type is a constraint that has been deferred until more information
    /// becomes available. When the constraint itself or one of its descendents is
    /// updated via unification, the constraint becomes active again.
    Deferred,
    /// The type is a constraint that has been solved. It is still part of the
    /// type set to allow other constraints to interact with it, but it no
    /// longer becomes active when it is changed.
    Solved,
    /// The state of all types that are not constraints.
    Inert,
    /// The state of a constraint that has been removed from a type set.
    /// This is used to allow solving subsets of a [`TypeSet`] in order to
    /// find a minimal error set.
    Removed,
}

#[derive(Debug, Clone, Copy)]
struct TypeData<L> {
    canonical: TypeIndex,
    slot: TypeSlot<L>,
    state: State,
}

#[derive(Debug, Clone, Copy)]
enum TypeSlot<L> {
    /// A type constructor with a given name and number of arguments.
    /// The arguments are [`TypeSlot::Arg`]s at type indices that directly
    /// follow the index of this type.
    Ctr(L, u16),
    /// A type variable that the is argument to a type constructor or the value/rest
    /// type of a row cons cell. The slot carries the index of the argument in the
    /// list of its parent's type arguments.
    Arg(u16),
    /// An empty row.
    RowEmpty,
    /// A row cons cell with a given label. The value and rest type of the row
    /// cons cell are [`TypeSlot::Arg`]s at type indices that directly follow
    /// the index of this type.
    RowCons(L),
    /// A type variable.
    Var,
    /// An inconsistent type. See [`TypeView::Error`].
    Error,
}

impl<L> TypeSlot<L> {
    fn priority(&self) -> usize {
        match self {
            TypeSlot::Ctr(_, _) => 1,
            TypeSlot::Arg(_) => 0,
            TypeSlot::RowEmpty => 1,
            TypeSlot::RowCons(_) => 1,
            TypeSlot::Var => 0,
            TypeSlot::Error => 2,
        }
    }
}

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

/// Iterator returned by [`TypeSet::parents`].
pub struct ParentsIter<'a, L> {
    types: &'a TypeSet<L>,
    inner: ClassIter<'a>,
}

impl<'a, L> Iterator for ParentsIter<'a, L>
where
    L: Eq + Copy,
{
    type Item = TypeIndex;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(index) = self.inner.next() {
            if let TypeSlot::Arg(i) = self.types.types[index].slot {
                return Some(TypeIndex::new(index - i as usize - 1));
            }
        }

        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.inner.len()))
    }
}

impl<'a, L> FusedIterator for ParentsIter<'a, L> where L: Eq + Copy {}

/// An error that occurred during type inference.
#[derive(Debug, Error)]
#[error("error while solving a constraint")]
pub struct SolveError(TypeIndex);

impl SolveError {
    pub fn new(constraint: TypeIndex) -> Self {
        SolveError(constraint)
    }

    pub fn constraint(&self) -> TypeIndex {
        self.0
    }
}

mod test {
    use crate::{util::extract_rec, TypeSet};

    #[test]
    fn test_rows() {
        let mut types = TypeSet::<u64>::new();

        let mut a = types.insert_row_empty();

        for i in (0..5).rev() {
            let (index, cons) = types.insert_row_cons(i);
            types.unify(cons.rest, a).unwrap();
            a = index;
        }

        let mut b = types.insert_row_empty();

        for i in 0..5 {
            let (index, cons) = types.insert_row_cons(i);
            types.unify(cons.rest, b).unwrap();
            b = index;
        }

        types.unify(a, b).unwrap();

        let a_rec = types.get_debug(a);
        let b_rec = types.get_debug(b);

        assert_eq!(a_rec, b_rec);
    }
}
