use fxhash::FxHashSet;
use std::hash::Hash;
use thiserror::Error;

use crate::{Type, TypeIndex, TypeSet};

/// Ensure uniqueness of row labels.
pub fn row_unique<L>(
    types: &mut TypeSet<L>,
    lacks_con: L,
    unique_con: L,
    mut row: TypeIndex,
) -> Result<bool, LacksError<L>>
where
    L: Hash + Ord + Copy,
{
    // TODO: Allow to avoid repeated allocation by passing in the set
    let mut seen = FxHashSet::default();

    while let Type::RowCons(cons) = types.get(row) {
        if !seen.insert(cons.label) {
            return Err(LacksError(row, cons.label));
        }

        row = cons.rest;
    }

    if let Type::Var(_) = types.get(row) {
        types.insert_con(unique_con, [Some(row)]);

        for label in seen.iter() {
            let (label_proxy, _) = types.insert_ctr(*label, []);
            types.insert_con(lacks_con, [Some(row), Some(label_proxy)]);
        }
    }

    Ok(true)
}

/// Ensure that a row lacks a label.
pub fn row_lacks<F, L>(
    types: &mut TypeSet<L>,
    lacks_con: L,
    label: L,
    mut row: TypeIndex,
) -> Result<bool, LacksError<L>>
where
    F: FnMut(L) -> L,
    L: Hash + Ord + Copy,
{
    let row_first = row;

    while let Type::RowCons(cons) = types.get(row) {
        if cons.label == label {
            return Err(LacksError(row, label));
        }

        row = cons.rest;
    }

    if types.canonical(row) == types.canonical(row_first) {
        return Ok(false);
    }

    if let Type::Var(_) = types.get(row) {
        let (label_proxy, _) = types.insert_ctr(label, []);
        types.insert_con(lacks_con, [Some(row), Some(label_proxy)]);
    }

    Ok(true)
}

// TODO: Row partition constraint
//
// /// Ensure that a row is the disjoint union of two others.
// pub fn row_partition<F, L>(
//     types: &mut TypeSet<L>,
//     mut label_to_lacks: F,
//     row_part_0: TypeIndex,
//     row_part_1: TypeIndex,
//     row_union: TypeIndex,
// ) -> Result<bool, LacksError<L>> {
//     todo!()
// }

#[derive(Debug, Clone, Error)]
#[error("lacks error")]
pub struct LacksError<L>(pub TypeIndex, pub L);

/// Ensure that a variable is never unified with any concrete type.
pub fn skolem_var<L>(types: &mut TypeSet<L>, var: TypeIndex) -> Result<(), SkolemError>
where
    L: Ord + Copy,
{
    if let Type::Var(_) = types.get(var) {
        Ok(())
    } else {
        Err(SkolemError(var))
    }
}

#[derive(Debug, Clone, Error)]
#[error("skolem error")]
pub struct SkolemError(pub TypeIndex);
