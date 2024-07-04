# Algebraic Data Types

## Records

A record is a product type with named fields, also known as a struct.

With rows we can represent the type of a record as follows:
We introduce a type constructor `Record r` where `r` must be a row that
determines the names and types of the record fields.
For example, `Record (name: String, age: Int)` is the type of records with the
fields name and age of type `String` and `Int`.
The type `Record ()` for the empty row `()` has exactly one value, and therefore
is the unit type.

Since rows in libra support duplicate labels, so would a record type `Record r`.
This might not be desired, for example when records are compiled to JavaScript maps
that must have distinct keys.
In that case the row `r` can be constrained to contain only unique labels.

With open rows we can represent extensible records, allowing us to write
functions that expect some record fields to be present but are indifferent about the presence of other fields.
For example, we can write a function `∀r. Record (x: Int | r) -> Int`
that accepts the records `{x: 1}`, `{x: 1, y: 2}`, `{x: 1, y: 2, z: 3}`
or any other record as long as it has a field `x` of type `Int`.
To manipulate records in general, we can define a family of functions ranging
over every label `l`:

 - `select(l): ∀a r. Record (l: a | r) -> a`
 - `restrict(l): ∀a r. Record (l: a | r) -> Record r`
 - `extend(j): ∀a r. Pair (Record r) a -> Record (l: a | r)`

Extensible records with row polymorphsim are similar to structural subtyping
(the exact relationship is [subtle](https://arxiv.org/pdf/2304.08267)).
There are some patterns that extensible records support that are hard to express
with subtyping:
We can, for example, write a function with type `∀r. Record (x: Int, y: Int | r) -> Record (xy: Int | r)` which replaces the `x` and `y` fields with an `xy` field in the record,
without changing the remaining fields.


## Variants

For every row `r` there is a type of variants (enums/sums/discriminated unions) `Variant r` so that `r` determines the names and associated types of each enum variant.
For example `Variant (ok: String, err: Error)` is the type which is either a `String`
labelled with `ok` or an `Error` labelled with `err`. The type `Variant ()` has no values, i.e. is the empty type.

When open rows are used for variants, we can express tagged unions in which not
 all variants are known. Consider for example a pattern matching expression
 `match x { foo x -> x, _ -> 0 }`. A type system building on Libra could assign
 `x` the variant type `Variant (foo: int | r)` where the row variable `r`
 represents all other cases that are caught by the wildcard case `_ -> 0`
 in the `match` expression.

 - `inject(j): ∀a r. a -> Variant (l: a | r)`
 - `embed(j): ∀a r. Variant l -> Variant (l: a | r)`
 - `decompose(j): ∀a r. Variant (l: a | r) -> Result a (Variant r)`
