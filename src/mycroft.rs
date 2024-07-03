use std::{
    collections::HashSet,
    hash::{BuildHasher, Hash},
};

use crate::{SolveError, TypeIndex, TypeSet};
use fxhash::FxHashSet;

/// Attempts to solve a set of constraints or reports errors.
///
/// In the case that the set of constraints is unsatisfiable, the algorithm from [A Practical
/// Framework for Type Inference Error Explanation] is used to compute a set of type errors:
/// We attempt to solve the constraint set and remove constraints until the constraint system
/// is solvable. To this end we keep track of a family of unsatisfiable cores, i.e. sets of
/// constraints that the solver reported to be unsatisfiable together. In each iteration
/// we remove a set of constraints which non-trivially intersects all unsatisfiable cores
/// that we have found so far.
///
/// [A Practical Framework for Type Inference Error Explanation]: https://dl.acm.org/doi/10.1145/2983990.2983994
pub fn run_mycroft<F, R, L>(type_set: &TypeSet<L>, mut solve: F) -> (R, TypeSet<L>)
where
    L: Eq + Copy,
    F: FnMut(&mut TypeSet<L>) -> Result<R, SolveError>,
{
    let mut unsat_cores: Vec<FxHashSet<TypeIndex>> = Vec::new();

    loop {
        let mut type_set_copy = type_set.clone();

        for index in hitting_set(unsat_cores.clone()) {
            type_set_copy.mark_removed(index);
        }

        match solve(&mut type_set_copy) {
            Ok(result) => return (result, type_set_copy),
            Err(SolveError) => unsat_cores.push(type_set_copy.unsat_core()),
        }
    }
}

/// Computes an approximate solution to the hitting set problem.
///
/// Given a family of sets, determine a minimal set which non-trivially intersects with each set in
/// the family. The hitting set problem is NP-hard, so this function computes a greedy approximation.
/// See [A Practical Framework for Type Inference Error Explanation] for more details.
///
/// [A Practical Framework for Type Inference Error Explanation]: https://dl.acm.org/doi/10.1145/2983990.2983994
fn hitting_set<T, S>(mut family: Vec<HashSet<T, S>>) -> HashSet<T, S>
where
    T: Eq + Hash + Copy,
    S: BuildHasher + Default,
{
    let mut hitting_set = HashSet::default();
    let union: HashSet<T, S> = family.iter().flatten().copied().collect();

    while !family.is_empty() {
        // todo: optimize this?
        let element = union
            .iter()
            .copied()
            .max_by_key(|element| family.iter().filter(|set| set.contains(element)).count())
            .unwrap();

        family.retain(|set| !set.contains(&element));
        hitting_set.insert(element);
    }

    hitting_set
}
