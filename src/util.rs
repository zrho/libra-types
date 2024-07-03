use crate::type_set::TypeSet;
use crate::{Type, TypeIndex};
use std::borrow::Borrow;
use std::fmt::Debug;
use std::sync::Arc;

/// A recursive representation of a type in a [`TypeSet`] for debugging.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DebugType<L> {
    Ctr(L, Arc<[Self]>),
    Var(TypeIndex),
    Row(DebugRow<L>),
    Error,
}

#[derive(Clone, PartialEq, Eq)]
pub struct DebugRow<L> {
    entries: Arc<[(L, DebugType<L>)]>,
    rest: Option<Arc<DebugType<L>>>,
}

impl<L> DebugRow<L> {
    #[inline]
    pub fn new_empty() -> Self {
        Self {
            entries: [].into(),
            rest: None,
        }
    }

    pub fn new_closed<I>(entries: I) -> Self
    where
        I: IntoIterator<Item = (L, DebugType<L>)>,
        L: Ord,
    {
        let mut entries = entries.into_iter().collect::<Vec<_>>();
        entries.sort_by(|(l1, _), (l2, _)| l1.cmp(l2));
        Self {
            entries: entries.into(),
            rest: None,
        }
    }

    #[inline]
    pub fn labels(&self) -> impl ExactSizeIterator<Item = &L> + '_ {
        self.entries.iter().map(|(label, _)| label)
    }

    #[inline]
    pub fn values(&self) -> impl ExactSizeIterator<Item = &DebugType<L>> + '_ {
        self.entries.iter().map(|(_, value)| value)
    }

    #[inline]
    pub fn iter(&self) -> impl ExactSizeIterator<Item = (&L, &DebugType<L>)> + '_ {
        self.entries.iter().map(|(label, value)| (label, value))
    }

    #[inline]
    pub fn rest(&self) -> Option<&DebugType<L>> {
        self.rest.as_ref().map(|rest| rest.borrow())
    }

    #[inline]
    pub fn is_proper(&self) -> bool {
        self.rest.is_none()
    }
}

impl<L> Debug for DebugRow<L>
where
    L: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut m = f.debug_map();
        m.entries(self.entries.iter().map(|(l, v)| (l, v)));

        if let Some(rest) = &self.rest {
            m.entry(&"...", rest);
        }

        m.finish()
    }
}

pub(crate) fn extract_rec<L, S, F>(
    types: &TypeSet<L>,
    mut resolve_label: F,
    index: TypeIndex,
) -> DebugType<S>
where
    F: FnMut(L) -> S + Copy,
    L: Eq + Copy,
    S: Ord,
{
    match types.get(index) {
        Type::Ctr(label, args) => {
            let label = resolve_label(label);
            let args = args
                .iter()
                .map(|arg| extract_rec(types, resolve_label, arg))
                .collect::<Vec<_>>()
                .into();
            DebugType::Ctr(label, args)
        }
        Type::Var(var) => DebugType::Var(var),
        Type::RowEmpty => DebugType::Row(DebugRow::new_empty()),
        Type::RowCons(_) => DebugType::Row(extract_row(types, resolve_label, index)),
        Type::Error => DebugType::Error,
    }
}

fn extract_row<L, S, F>(
    types: &TypeSet<L>,
    mut resolve_label: F,
    mut index: TypeIndex,
) -> DebugRow<S>
where
    F: FnMut(L) -> S + Copy,
    L: Eq + Copy,
    S: Ord,
{
    let mut entries = Vec::new();

    let rest = loop {
        match types.get(index) {
            Type::RowCons(cons) => {
                let label = resolve_label(cons.label);
                let value = extract_rec(types, resolve_label, cons.value);
                entries.push((label, value));
                index = cons.rest;
            }
            Type::RowEmpty => break None,
            _ => break Some(index),
        }
    };

    entries.sort_by(|(l1, _), (l2, _)| l1.cmp(l2));

    let rest = rest.map(|rest| Arc::new(extract_rec(types, resolve_label, rest)));

    DebugRow {
        entries: entries.into(),
        rest,
    }
}
