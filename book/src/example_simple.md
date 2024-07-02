# Example

```rust,no_run
{{#include ../../examples/simple.rs:expr}}
```
```rust,no_run
{{#include ../../examples/simple.rs:type}}
```

## Constraint Generation

```rust,no_run
impl Generate {
{{#include ../../examples/simple.rs:generate}}
}
```

```rust,no_run
impl Generate {
{{#include ../../examples/simple.rs:generate_apply}}
}
```

```rust,no_run
impl Generate {
{{#include ../../examples/simple.rs:generate_fun}}
}
```

```rust,no_run
impl Generate {
{{#include ../../examples/simple.rs:generate_var}}
}
```

```rust,no_run
impl Generate {
{{#include ../../examples/simple.rs:generate_let}}
}
```

## Constraint Solving

```rust,no_run
{{#include ../../examples/simple.rs:solve_loop}}
```

## Type Extraction

```rust,no_run
{{#include ../../examples/simple.rs:extract_type}}
```

```rust,no_run
{{#include ../../examples/simple.rs:extract_type_schema}}
```
