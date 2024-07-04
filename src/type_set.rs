use std::iter::FusedIterator;

use fxhash::FxHashSet;
use thiserror::Error;

use crate::{
    union_find::{ClassIter, UnionFind},
    util::{extract_rec, DebugType},
    Children, RowCons, Type, TypeIndex,
};

/// A set of types and type constraints.
///
/// Types and constraints are represented uniformly.
///
/// Cloning a TypeSet is O(n). This is not entirely ideal since the Mycroft
/// error reporting scheme needs a clone for every iteration, including the
/// first one for the happy case in which no type errors occur. So far we
/// haven’t found a way to avoid this without a performance penalty in practice.
/// Instead we ensure that cloning a TypeSet amounts to a small and constant
/// number of heap allocations and calls to memcpy.
#[derive(Debug, Clone)]
pub struct TypeSet<L> {
    uf: UnionFind,
    types: Vec<TypeData<L>>,
    errors: Vec<TypeIndex>,
    active: Vec<TypeIndex>,
}

impl<L> TypeSet<L>
where
    L: Ord + Copy,
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

    /// Insert a type constructor.
    ///
    /// # Example
    ///
    /// ```
    /// # use libra_types::{TypeSet, Type};
    /// let mut types = TypeSet::<u32>::new();
    ///
    /// const TYPE_INT: u32 = 0;
    /// const TYPE_MAP: u32 = 1;
    ///
    /// let (int, _) = types.insert_ctr(TYPE_INT, []);
    /// let (_, map_args) = types.insert_ctr(TYPE_MAP, [Some(int), None]);
    ///
    /// assert_eq!(types.canonical(map_args.get(0)), types.canonical(int));
    /// assert!(matches!(types.get(map_args.get(1)), Type::Var(_)));
    /// ```
    pub fn insert_ctr<I>(&mut self, label: L, args: I) -> (TypeIndex, Children)
    where
        I: IntoIterator<Item = Option<TypeIndex>>,
        I::IntoIter: ExactSizeIterator,
    {
        let args = args.into_iter();
        let arity = args.len() as u16;
        let index = self.insert_slot(TypeSlot::Ctr(label, arity), State::Inert);

        for (i, arg) in args.enumerate() {
            let arg_index = self.insert_slot(TypeSlot::Arg(i as u16), State::Inert);

            if let Some(arg_given) = arg {
                // This unification always succeeds since `arg_index` is a fresh type variable.
                self.unify(arg_given, arg_index).unwrap();
            }
        }

        let children = Children { index, len: arity };
        (index, children)
    }

    /// Insert a type constraint.
    ///
    /// This method works analogously to [`TypeSet::insert_ctr`], except that
    /// it additionally marks the inserted type constructor as an active constraint.
    /// In particular the index of the newly inserted constraint will be returned
    /// by [`TypeSet::pop_active`] at some point so that the constraint can be discharged.
    pub fn insert_con<I>(&mut self, label: L, args: I) -> (TypeIndex, Children)
    where
        I: IntoIterator<Item = Option<TypeIndex>>,
        I::IntoIter: ExactSizeIterator,
    {
        let (index, children) = self.insert_ctr(label, args);
        self.types[index.index()].state = State::Active;
        self.active.push(index);
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
        let t = self.get_type_internal(self.canonical(index));

        if let Type::Var(_) = t {
            for i in self.uf.iter_class(index.index()) {
                match self.types[i].slot {
                    TypeSlot::Ctr(_, _)
                    | TypeSlot::RowEmpty
                    | TypeSlot::RowCons(_)
                    | TypeSlot::Error => panic!(),
                    _ => {}
                }
            }
        }

        t
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
    pub fn unify(&mut self, a: TypeIndex, b: TypeIndex) -> Result<(), UnifyError> {
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
            (Type::Error, _) | (_, Type::Error) => {}
            (Type::Var(_), _) | (_, Type::Var(_)) => {}

            (Type::Ctr(a_label, a_args), Type::Ctr(b_label, b_args)) => {
                if a_label != b_label {
                    self.record_error(a);
                    return Err(UnifyError::Mismatch(a));
                }

                if a_args.len() != b_args.len() {
                    self.record_error(a);
                    return Err(UnifyError::Mismatch(a));
                }

                for (a_arg, b_arg) in a_args.iter().zip(b_args) {
                    // TODO: Error context?
                    self.unify(a_arg, b_arg)?;
                }
            }

            (Type::RowEmpty, Type::RowEmpty) => {}
            (Type::RowCons(_), Type::RowCons(_)) => {
                self.unify_rows(a, b)?;
            }

            _ => {
                self.record_error(a);
                return Err(UnifyError::Mismatch(a));
            }
        };

        Ok(())
    }

    fn unify_check_cycle(&mut self, start: TypeIndex) -> Result<(), UnifyError> {
        let start = self.canonical(start);

        // TODO: Reuse these allocations?
        let mut stack: Vec<_> = self.parents(start).collect();
        let mut visited = FxHashSet::default();

        while let Some(index) = stack.pop() {
            let index = self.canonical(index);

            if !visited.insert(index) {
                continue;
            }

            if index == start {
                self.record_error(start);
                return Err(UnifyError::Cycle(start));
            }

            if let State::Deferred = self.state(index) {
                self.types[index.index()].state = State::Active;
                self.active.push(index);
            }

            stack.extend(self.parents(index));
        }

        Ok(())
    }

    /// Helper for [`Self::unify`] to unify two rows.
    fn unify_rows(&mut self, a: TypeIndex, b: TypeIndex) -> Result<(), UnifyError> {
        // TODO: Can we avoid the allocation here? We could at least reuse it.
        let (a_entries, mut a_rest) = self.collect_sorted_row(a);
        let (b_entries, mut b_rest) = self.collect_sorted_row(b);

        // TODO: Provide context in the unify error?
        for merged in util::merge_outer_join(a_entries, b_entries) {
            match merged {
                util::Merged::Left(label, value) => {
                    let (cons_ix, cons) = self.insert_row_cons(label);
                    self.unify(cons.value, value)?;
                    self.unify(b_rest, cons_ix)?;
                    b_rest = cons.rest;
                }
                util::Merged::Right(label, value) => {
                    let (cons_ix, cons) = self.insert_row_cons(label);
                    self.unify(cons.value, value)?;
                    self.unify(a_rest, cons_ix)?;
                    a_rest = cons.rest;
                }
                util::Merged::Both(_, a_value, b_value) => {
                    self.unify(a_value, b_value)?;
                }
            }
        }

        self.unify(a_rest, b_rest)?;
        Ok(())
    }

    /// Collect all entries of a row and sort them by their key.
    /// Returns the sorted entries and the tail of the row.
    /// The sort by key is stable so that the order of duplicate entries
    /// is preserved.
    fn collect_sorted_row(&mut self, mut index: TypeIndex) -> (Vec<(L, TypeIndex)>, TypeIndex) {
        let mut entries = Vec::new();

        while let Type::RowCons(cons) = self.get(index) {
            entries.push((cons.label, cons.value));
            index = cons.rest;
        }

        entries.sort_by_key(|(l, _)| *l);

        (entries, index)
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
            let index = self.canonical(index);

            if !visited.insert(index) {
                continue;
            }

            stack.extend(self.parents(index));

            if let State::Active | State::Solved = self.state(index) {
                // Constraints can be unified with each other for deduplication.
                // To ensure that we get the indices of all constraints that
                // were involved in the error, we need to iterate over the
                // concrete indices in the constraint's equivalence class.
                for concrete_index in self.iter_class(index) {
                    if let Type::Ctr(_, cs) = self.get_type_internal(concrete_index) {
                        unsat_core.insert(index);
                        stack.extend(cs);
                    }
                }
            }
        }

        unsat_core
    }

    #[inline]
    fn iter_class(&self, index: TypeIndex) -> impl ExactSizeIterator<Item = TypeIndex> + '_ {
        self.uf.iter_class(index.index()).map(TypeIndex::new)
    }

    #[inline]
    pub fn mark_solved(&mut self, index: TypeIndex) {
        let index = self.canonical(index);
        if let State::Active = self.types[index.index()].state {
            self.types[index.index()].state = State::Solved;
        }
    }

    #[inline]
    pub fn mark_removed(&mut self, index: TypeIndex) {
        let index = self.canonical(index);
        self.types[index.index()].state = State::Removed;
    }

    #[inline]
    pub fn state(&self, index: TypeIndex) -> State {
        let index = self.canonical(index);
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

            if self.types[index.index()].state != State::Active {
                continue;
            }

            self.types[index.index()].state = State::Deferred;

            let Type::Ctr(label, cs) = self.get(index) else {
                panic!("invariant: a constraint must have been a type constructor");
            };

            return Some((index, label, cs));
        }

        None
    }

    #[inline]
    pub fn size(&self) -> usize {
        self.types.len()
    }
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

// TODO: Include more information in `UnifyError`.

/// Error while unifying types.
#[derive(Debug, Clone, Error)]
pub enum UnifyError {
    #[error("unification created a cycle")]
    Cycle(TypeIndex),
    #[error("mismatch")]
    Mismatch(TypeIndex),
}

/// An error that occurred during type inference.
#[derive(Debug, Clone, Error)]
#[error("type error while solving constraints")]
pub struct SolveError;

impl From<UnifyError> for SolveError {
    fn from(_: UnifyError) -> Self {
        SolveError
    }
}

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

mod util {
    use std::iter::Peekable;

    #[derive(Debug, Clone, Copy)]
    pub enum Merged<K, V> {
        /// The key was present only in the left collection.
        Left(K, V),
        /// The key was present only in the right collection.
        Right(K, V),
        /// The key was present in both collections
        Both(K, V, V),
    }

    /// Perform an outer join on two collections of key/value pairs, sorted by key.
    pub fn merge_outer_join<I, J, K, V>(
        left: I,
        right: J,
    ) -> MergeOuterJoin<I::IntoIter, J::IntoIter>
    where
        I: IntoIterator,
        J: IntoIterator,
        I::IntoIter: Iterator<Item = (K, V)>,
        J::IntoIter: Iterator<Item = (K, V)>,
        K: Ord,
    {
        MergeOuterJoin {
            left: left.into_iter().peekable(),
            right: right.into_iter().peekable(),
        }
    }

    /// Iterator returned by [`merge_outer_join`].
    pub struct MergeOuterJoin<I, J>
    where
        I: Iterator,
        J: Iterator,
    {
        left: Peekable<I>,
        right: Peekable<J>,
    }

    impl<I, J, K, V> Iterator for MergeOuterJoin<I, J>
    where
        I: Iterator<Item = (K, V)>,
        J: Iterator<Item = (K, V)>,
        K: Ord,
    {
        type Item = Merged<K, V>;

        fn next(&mut self) -> Option<Self::Item> {
            use std::cmp::Ordering;

            match (self.left.peek(), self.right.peek()) {
                (None, None) => None,
                (None, Some(_)) => {
                    let (k, v) = self.right.next()?;
                    Some(Merged::Right(k, v))
                }
                (Some(_), None) => {
                    let (k, v) = self.left.next()?;
                    Some(Merged::Left(k, v))
                }
                (Some((k_left, _)), Some((k_right, _))) => match k_left.cmp(k_right) {
                    Ordering::Less => {
                        let (k, v) = self.left.next()?;
                        Some(Merged::Left(k, v))
                    }
                    Ordering::Equal => {
                        let (k, v_left) = self.left.next()?;
                        let (_, v_right) = self.right.next()?;
                        Some(Merged::Both(k, v_left, v_right))
                    }
                    Ordering::Greater => {
                        let (k, v) = self.right.next()?;
                        Some(Merged::Right(k, v))
                    }
                },
            }
        }

        fn size_hint(&self) -> (usize, Option<usize>) {
            let (left_min, left_max) = self.left.size_hint();
            let (right_min, right_max) = self.right.size_hint();

            let min = std::cmp::max(left_min, right_min);

            let max = match (left_max, right_max) {
                (Some(left_max), Some(right_max)) => Some(left_max + right_max),
                _ => None,
            };

            (min, max)
        }
    }
}
