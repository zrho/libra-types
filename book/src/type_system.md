# The Type System

Libra implements a type system with parametric polymorphism inspired by
[Hindley-Milner] but extended with a user-definable constraint language
as in [`HM(X)`]. Through this extensible constraint language, a variety of
type system features can be built upon Libra.

 - **Extensibility:** 
 - **Completeness:**
 - **Performance:**

## Polymorphism

Since the type system is polymorphic, the type of a term can be left partially
unspecified through type variables. 
This allows us to write generic functions such as `rev: ∀a. List a -> List a` or
`swap : ∀a b. Pair a b -> Pair b a`.
Assuming the constraint system is well-behaved, Libra infers [principal types]
for every term, i.e. a polymorphic type scheme so that every well-typed usage of the term
is an instance of the inferred type.
Principal types allow us to perform type inference on parts of a bigger program in isolation
for modular, parallel and incremental compilation. 

To keep type inference complete and decidable, we restrict to rank 1 polymorphism:
universal quantifiers may not occur nested within a type. This is not a big
restriction in practice, and higher rank types can be simulated with data types
and existentials where desired.
We also believe that [let should not be generalised](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/tldi10-vytiniotis.pdf).
Classical Hindley Milner type systems perform type generalisation at local
let bindings, so that local variables are always assigned a polymorphic type.
For example the expression `let f = λx. x in (f 0, f true)` would be well-typed
classically, with the local variable `f` being assigned the type `∀a. a -> a`.
Unfortunately this system is incompatible with a general
and extensible constraint system. We therefore do not implement support
for local implicit generalisation in libra. That design choice also paves
the way for potential future support of [local assumptions](https://simon.peytonjones.org/outsideinx/)
and in particular GADTs.

## Row Types

Rows are labelled collections of types.
Rows can be used to model [extensible records and variants] and
[algebraic effects].
Concretely a row is either the empty row `()`,
a type variable `r` or a row extension `(l : t | r)` where `t`, `r` are types
and `l` is a label. By unrolling consecutive row extensions we can write a row
as `(l_1 : t_1, ..., l_n : t_n | r)` where `r` is one of the following:

 - **Closed Row:** `r` is an empty row `()`.
 - **Open Row:** `r` is a type variable.
 - **Improper Row:** `r` is any other type.

Through open rows we enable row polymorphism, on top of which we can build [extensible records and variants] and [effect polymorphism].
Improper rows are unusual and a type system that is built upon Libra might want
to exclude them, either by construction or by using the constraint system.
We allow improper rows to avoid picking a kind system in Libra.

Rows support [scoped labels]: row extensions with different labels can
be exchanged freely, while the order of entries with the same label must be
preserved.
For instance we consider the rows `(x: Int, y: Float | r)` and `(y: Float, x: Int | r)`
to be equal, while `(x: Int, x: Float | r)` and `(x: Float, x: Int | r)` are valid
but different.
In cases where duplicate labels are not desired, this can be enforced
by using custom constraints.
Duplicate labels can be useful to for [scoped effects].

The label `l` in a row extension `(l : t | r)` is always a constant and can
not be polymorphic.
While we do not support rows with [first class labels] directly,
this feature can be (partly) simulated using constraints.

## Type Constraints

Type constraints are the primary mechanism of extensibility in Libra and
can be used to implement a variety of type system features.


*Principal types and constraints*

 <!-- - `Eq a`: Requires `a` to have a canonical equality operation. -->
 <!-- - `Unique r`: Requires `r` to be a row without duplicate labels. -->
 <!-- - `Inst(s) t`: Requires `t` to be an instance of a type scheme `s`. -->

<!-- A programming language with linear types can assign the type -->
<!-- `∀a. Copy a => a -> Pair a a` -->
<!-- to the expression -->
<!-- `λx. (x, x)` -->
<!-- to denote the requirement that the type of `x` must be copyable. -->

[scoped labels]: https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/scopedlabels.pdf
[first class labels]: https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/fclabels.pdf
[Hindley-Milner]: https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system
[`HM(X)`]: https://www.cs.tufts.edu/~nr/drop/tapos-final.pdf
[principal types]: https://en.wikipedia.org/wiki/Principal_type
[algebraic effects]: ./recipe_effects.md
[extensible records and variants]: ./recipe_adt.md
[effect polymorphism]: ./recipe_effects.md#extensible-records-and-variants
[scoped effects]: ./recipe_effect.md#scoped-effects
