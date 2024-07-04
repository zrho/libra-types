# Algebraic Effects

[Algebraic effects] are an approach to modelling a program's side effects.
Row typing can be used to capture a function's effects in the function type.
This approach is taken by the programming language [Koka] and described in
detail [here][effect rows].
Libra can be used to implement a similar typing scheme for algebraic effects.

We can introduce a type constructor `a -[e]-> b` where `a` and `b` are input and output
type of the function, and `e` is a row of effects.
When `e` is the empty row, the function may perform no side effects and so
`a -[()]- b` is the type of pure functions from `a` to `b`.
To keep the notation readable, we will write `a -> b` for `a -[()]-> b`.

 - `length: ∀e. String -[e]-> Int`
 - `read-line: ∀e. Unit -[io: * | e]-> String`
 - `throw: ∀e a. a -[exn: a | e]->  Unit`

Polymorphism over the row of effects can be used for higher order functions:

 - `list-map: ∀a b e. (a -[e]-> b) -> List a -[e]-> List b`
 - `catch: ∀a b x. (a -[exn: x | e]-> b) -> (a -[e]-> Result b x)`
 - `map-exn: ∀a b x y e. (x -[e]-> y) -> (a -[exn: x | e]-> b) -> (a -[exn: y | e]-> b)`

## Unions through Polymorphism

When effectful functions are used together in one composite function, 
the function's effect row should be the union of the individual effects.
By using row polymorphism, the union can be computed iin Libra using unification.

Consider for example the program that uses the three functions that we defined above:

```txt
let read-non-empty = λ () ->
  let line = read-line () in
  if length line == 0 then
    throw EmptyLine
  else
    line
```

When we instantiate the types of `length`, `read-line` and `throw` into a `TypeSet`,
we end up with the following situation (only showing those types that are relevant
to the effects):

```
?0 [type variable e of length]
?1 [type variable e of read-line]
?2 = *
?3 = (io: ?2 | ?1)
?4 [type variable e of throw]
?5 [type variable a of throw]
?6 = (exn: ?5 | ?4)
```

Using `length`, `read-line` and `throw` together in one function requires us to
unify their effect rows, and so we record additional unification constraints
`?0 ~ ?3` and `?3 ~ ?6`.
Solving these constraints, we end up with `?0` being bound to the open row
`(io: *, exn: ?5 | ?7)` for a new type variable `?7`.
The type scheme that is inferred for the function `read-non-empty` therefore
is `∀e. Unit -[io: *, exn: EmptyLine | e]-> String`, indicating that the function
both uses io and can throw exceptions.



## Implicit Opening and Closing

 - **TODO:** implicit opening and closing of effect rows

When instantiating the type scheme of a function with an effect type, 
we implicitly open the row of effects. Conversely, after inferring the type
of a function, we can close the effect rows. This allows us to write the
simpler types: 

 - `length: String -> Int`
 - `read-line: Unit -[io: *]-> String`
 - `throw: ∀a. a -[exn: a]-> Unit`

## Scoped Labels for Scoped Handlers

 - **TODO:** scoped labels for scoped effect handlers

[Koka]: https://koka-lang.github.io/koka/doc/index.html
[effect rows]: https://www.microsoft.com/en-us/research/wp-content/uploads/2016/12/algeff.pdf
[algebraic effects]: https://homepages.inf.ed.ac.uk/gdp/publications/alg_ops_gen_effects.pdf
