# Type Errors

A type inference engine should not only work when the program is well-typed,
but also allow for diagnostics in case of a type error.
Producing helpful diagnostics is a difficult and underspecified problem.
Classical implementations of Hindley Milner type inference stop at the first
type error that is encountered, which due to the non-local nature of unification
may also be far from the location of the actual mistake in the code.

Libra is designed to be used with the
[Mycroft](https://dl.acm.org/doi/abs/10.1145/3022671.2983994)
approach to error reporting.
When Libra encounters an error, it can produce an *unsatisfiable core*, i.e.
a subset of the type constraints which can not be simultaneously satisfied.
The unsatisfiable core can then be used to selectively disable individual
constraints until a (close to) minimal set of constraints is found without
which the type inference problem is satisfiable.
These error constraints can then be used to produce the appropriate error messages.
This approach for error reporting was chosen since it can produce decent
quality type errors, does not stop at the first error but reports multiple
errors, and allows for extensibility in the constraint language.

In the case of an error, Mycroft runs the type inference engine many times.
Depending on the size of the program and the complexity of the custom
constraint language, this process may be slow.
For situations where high quality error messages are not necessary,
the repeated resolving may be skipped and the ill-typed program rejected
immediately.
