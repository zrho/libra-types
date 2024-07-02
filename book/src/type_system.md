# The Type System

## Polymorphism

We believe that [let should not be generalised](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/tldi10-vytiniotis.pdf).
Classical Hindley Milner type systems perform type generalisation at local
let bindings. Unfortunately this system is incompatible with a general
and extensible constraint system. We therefore do not implement support
for local implicit generalisation in libra. That design choice also paves
the way for potential future support of [local assumptions](https://simon.peytonjones.org/outsideinx/).

## Row Types

Libra supports a form of row types with [scoped labels].
Rows can be used to model extensible records, variant and effects.
A row is a sequence of row cons cells, specifying a label, a type and the
rest of the row.
Entries with different labels can be exchanged freely, while the order
of entries with the same label must be preserved.
This avoids label conflicts when using row polymorphism.
In cases where duplicate labels are not desired, this can be enforced
by using custom constraints.

Depending on the type that the row ends in, we classify rows as follows:
 - **Closed Row:** The sequence ends in an empty row.
 - **Open Row:** The sequence ends in a row variable.
 - **Improper Row:** The sequence ends in a type that is not a row.

We currently do not support rows with [first class labels] directly,
but this feature can be (partly) simulated using constraints as well.

## Constraint Based Type Inference

The intended usage of Libra is to infer or check the types of a program
in three stages:

 1. **Constraint Generation:** We traverse the input program and generate
    types and type constraints in a `TypeSet` that together describe the type inference
    problem associated to the program. During this process we keep track of
    the association between locations in the program and the `TypeIndex`s
    in the `TypeSet` that should correspond to the type of that program location.

 2. **Constraint Solving:** Once all types and constraints are collected in the
    `TypeSet`, we solve the type constraints. The `TypeSet` keeps track of
    constraints that remain unsolved. For any such constraint, a user provided
    procedure uses unification to incorporate the knowledge encoded in the
    constraint into the `TypeSet`. The procedure can then decide whether to
    consider the constraint solved, to signal an error or to postpone solving
    the constraint to when more information becomes known.
    Postponed constraints are reawakened when one of their referenced types changes.

  
 3. **Elaboration:** After all constraints are solved, we extract the type information
    from the `TypeSet` to generate a program representation with type annotations.
    This step uses the association between `TypeIndex`s and program locations that
    has been recorded in the constraint generation step.

  [scoped labels]: https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/scopedlabels.pdf
  [first class labels]: https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/fclabels.pdf
