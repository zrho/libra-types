# Algebraic Data Types

## Extensible Records and Variants

In the case of record types, open rows allow us to write functions that expect some fields to be present but are indifferent about the presence of other fields.
For example, we can write a function `∀r. Record (x: Int | r) -> Int`
that accepts the records `{x: 1}`, `{x: 1, y: 2}`, `{x: 1, y: 2, z: 3}`
or any other record as long as it has a field `x` of type `Int`.

This is similar to subtyping, but more expressive:
We can, for example, write a function with type `∀r. Record (x: Int, y: Int | r) -> Record (xy: Int | r)` which replaces the `x` and `y` fields with an `xy` field in the record,
without changing the remaining fields.

When open rows are used for variants, we can express tagged unions in which not
 all variants are known. Consider for example a pattern matching expression
 `match x { foo x -> x, _ -> 0 }`. A type system building on Libra could assign
 `x` the variant type `Variant (foo: int | r)` where the row variable `r`
 represents all other cases that are caught by the wildcard case `_ -> 0`
 in the `match` expression.   
