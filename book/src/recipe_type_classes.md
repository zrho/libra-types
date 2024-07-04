# Type Classes

A function with a polymorphic argument must work with values of any type.
This is fine for a function like `rev: ∀a. List a -> List a` that reverse a
list without looking at its elements.
However some polymorphic functions might need to assume additional stucture
on their type arguments.
A sorting function for lists can not be given the type `∀a. List a -> List a`
since it requires the type `a` to be ordered.
This can be expressed via type class `Ord`, giving the sort function the type
`∀a. Ord a => List a -> List a`.

Type classes can be expressed naturally using Libra's constraint system.

## Instantiation

Suppose that we encounter the `sort` function in the constraint generation
phase of the type inference algorithm. We look up the type schema of `sort`
in the environment and find it to be `∀a. Ord a => List a -> List a`.
We instantiate the type parameter `a` with a new type variable `?0` and
recursively insert the `List` and `->` type constructors into the `TypeSet` as usual.
The type class constraint `Ord a` then translates into a new constraint `Ord ?0`
in the typeset. Overall, we have inserted five new entries:

```txt
?0
?1 = List ?0
?2 = List ?0
?3 = -> ?0 ?1
?4 = Ord ?0
```

## Solving

In the instantiation step, a type class constraint is translated into a constraint
in the `TypeSet`. The constraint starts out as active and therefore will at some
point show up in the solver loop.

When the type of the constraint's argument has become concrete enough,
we might be able to solve the constraint directly. For example, when we see
a constraint `Ord ?0` and `?0` is bound to `Int`, we can mark the constraint
as solved after assuring ourselves that `Int`s can be ordered. Otherwise,
the constraint becomes deferred, to be considered again once more information
is available.

 - **TODO** Implication

`Ord a, Ord b => Ord (Pair a b)`.
In this case, when we encounter a constraint `Ord (Pair ?0 ?1)` we can immediately
solve it by inserting new constraints `Ord ?0` and `Ord ?1` into the type set.


At this point we may also perform deduplication:
When we notice that a type is constrained multiple times by the same type class,
we can unify the constraints. This is possible since constraints are themselves
just type constructors in the `TypeSet`.
By deduplicating the constraints, we avoid solving them multiple times,
which might be helpful for deeply nested generic types.
Deduplication is also important for subsumption checking and evidence translation.

 - **TODO** What happens with the constaint's state after unification?
 
## Subsumption

 - **TODO** Subsumption
 - **TODO** Write about unconstrained subsumption before (requires skolem vars).
 
## Evidence translation
 
 - **TODO** Evidence translation
