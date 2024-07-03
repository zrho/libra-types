# Type Inference

The indended usage for Libra is to build a type inference algorithm
that proceeds in three steps.

## Constraint Generation

In the constraint generation step, we traverse the input program to generate
a collection of types and type constraints that together describe the type
inference problem posed by the program.
During this process, we may keep track of the association of the generated
types and constraints with the associated locations in the program.
This additional data can then be used in the later elaboration step,
or to improve error messages should be program have a type error.

For example, when implementing type inference for the lambda calculus,
the constraint generation process would proceed as follows:

 - When we encounter a function application `f e` we first recursively generate
   the type constraints for `f` and `e`, obtaining type variables `a` and `b`
   so that `f: a` and `e: b`. We then record a unification constraint between
   `a` and the function type `b -> c` for a fresh type variable `c`. Then
   `c` is reported as the type of `f e`.
 - For a lambda term `λx. e` we generate a fresh type variable `a`. We insert
   the association `x: a` into a context and recursively generate the type
   constraints for `e`, obtaining a type variable `b` with `e: b`.
   The type of `λx. e` is then reported to be the function type `a -> b`.
 - For a variable `x`, we look up `x` in the context. If we find `x` in the
   context, we return its type as recorded in the context. Otherwise we fail
   with a scope error.

## Constraint Solving

Once all types and constraints are collected in the
`TypeSet`, we solve the type constraints. The `TypeSet` keeps track of
constraints that remain unsolved. For any such constraint, a user provided
procedure uses unification to incorporate the knowledge encoded in the
constraint into the `TypeSet`. The procedure can then decide whether to
consider the constraint solved, to signal an error or to postpone solving
the constraint to when more information becomes known.
Postponed constraints are reawakened when one of their referenced types changes.

## Elaboration

After all constraints are solved, we extract the type information
from the `TypeSet` to generate a program representation with type annotations.
This step uses the association between `TypeIndex`s and program locations that
has been recorded in the constraint generation step.
