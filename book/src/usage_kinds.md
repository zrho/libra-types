## Kinds

Libra does not directly represent kinds.
Instead, a kind system can be built using constraints as follows:
for every type constructor we know the kind and so do not need to represent it explicitly.
To signify that a type variable must have a specific kind, we create a new constraint.
Whenever the constraint becomes active, we can check if the type variable has since been unified with a type whose kind is known.
