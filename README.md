# RulesXP

[![CI](https://github.com/microsoft/rulesxp/workflows/CI/badge.svg)](https://github.com/microsoft/rulesxp/actions/workflows/ci.yml)
[![Crates.io](https://img.shields.io/crates/v/rulesxp.svg)](https://crates.io/crates/rulesxp)
[![Documentation](https://docs.rs/rulesxp/badge.svg)](https://docs.rs/rulesxp)

**Multi-Language Rules Expression Evaluator**

RulesXP is a minimalistic expression evaluator that supports both JSONLogic and Scheme syntax with strict typing.
It's designed for reliable rule evaluation with predictable behavior.

**Note that this project is a work in progress and the API and feature set are expected to change**

## Features

### Dual Language Support
The project supports minimalistic subsets of:
- **[JSONLogic](https://jsonlogic.com/)**: JSON-based rules engine syntax
- **[Scheme R7RS](https://en.wikipedia.org/wiki/Scheme_\(programming_language\))**: Small Lisp-family functional programming syntax

### Strict Typing
- **No Type Coercion**: `1 !== "1"` and `0 !== false`. No "truthiness" or automatic conversions
- **Type Error Detection**: Type mismatches caught at evaluation time

### Core Data Types
- **Numbers**: 64-bit integers (`42`, `-5`, `#xFF`)
- **Booleans**: `true`/`false` (JSONLogic) or `#t`/`#f` (Scheme)
- **Strings**: `"hello world"`
- **Lists**: `[1,2,3]` (JSONLogic) or `(list 1 2 3)` (Scheme)
- **Symbols**: Identifiers like `foo`, `+`, `>=`

## Language Examples

### JSONLogic Syntax
```jsonc
{"===": [1, 1]}           // Strict equality
{"and": [true, false]}    // Boolean logic
{"+": [1, 2, 3]}         // Arithmetic
{"if": [true, "yes", "no"]} // Conditionals
{"<": [1, 2, 3]}         // Chained comparisons
```

### Scheme Syntax
```scheme
(equal? 1 1)             ; Strict equality
(and #t #f)              ; Boolean logic
(+ 1 2 3)                ; Arithmetic
(if #t "yes" "no")       ; Conditionals
(< 1 2 3)                ; Chained comparisons
```

### Equivalence Examples
| JSONLogic | Scheme | Result |
|-----------|--------|--------|
| `{"===": [1, 1]}` | `(equal? 1 1)` | `true` |
| `{"!==": [1, 2]}` | `(not (equal? 1 2))` | `true` |
| `{"+": [1, 2]}` | `(+ 1 2)` | `3` |
| `{"and": [true, {">":[5,3]}]}` | `(and #t (> 5 3))` | `true` |

## Installation & Usage

### As a Library
Add to your `Cargo.toml`:
```toml
[dependencies]
rulesxp = "0.1.0"
```

### Basic Usage
```rust
use rulesxp::{jsonlogic::parse_jsonlogic, scheme::parse_scheme, evaluator::*};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut env = create_global_env();

    // JSONLogic evaluation
    let jsonlogic_expr = parse_jsonlogic(r#"{"and": [true, {">": [5, 3]}]}"#)?;
    let result = eval(&jsonlogic_expr, &mut env)?;
    println!("Result: {}", result); // true

    // Scheme evaluation
    let scheme_expr = parse_scheme("(and #t (> 5 3))")?;
    let result = eval(&scheme_expr, &mut env)?;
    println!("Result: {}", result); // #t

    Ok(())
}
```

### Registering Custom Builtins

You can extend the evaluator with your own builtins. There are two
APIs, both of which end up using the same underlying machinery:

1. **Raw slice API** (closest to the core engine):

```rust
use rulesxp::ast::Value;
use rulesxp::evaluator::{create_global_env, Environment};
use rulesxp::Error;

fn my_custom_function(args: &[Value]) -> Result<Value, Error> {
    println!("called with {} args", args.len());
    Ok(Value::Unspecified)
}

let mut env: Environment = create_global_env();
env.register_builtin_function("my-func", my_custom_function);
// Now (my-func) / {"my-func": [...]} can be used from Scheme / JSONLogic
```

2. **Typed API** (ergonomic Rust signatures, automatic conversion):

```rust
use rulesxp::ast::Value;
use rulesxp::evaluator::{create_global_env, Environment};

// Fixed arity: arguments are converted from `Value` automatically
fn add2(a: i64, b: i64) -> i64 {
    a + b
}

// Zero-argument builtin
fn forty_two() -> i64 { 42 }

// List argument converted to a slice of `Value`
fn first_and_list_len(args: &[Value]) -> Value {
    Value::List(vec![
        args.first().cloned().unwrap_or(Value::Unspecified),
        Value::Number(args.len() as i64),
    ])
}

let mut env: Environment = create_global_env();
env.register_builtin_operation("add2", add2);
env.register_builtin_operation("forty-two", forty_two);
env.register_builtin_operation("first-and-len", first_and_list_len);

// These builtins are then available from evaluated expressions
```

The typed API currently supports:

- **Parameter types**: `i64`, `bool`, `&str`, borrowed values `&Value`,
    and list arguments via slices such as `&[i64]`, `&[bool]`, `&[&str]`,
    and `&[Value]` (when the call site passes a list value).
- **Return types**: any type implementing the internal `IntoValue` trait
    (currently `Value`, `i64`, `bool`, `String`, and `&str`), or
    `Result<R, E>` where `R` is one of those and `E: Display`.

Arity is enforced automatically; conversion errors become `TypeError`,
and any user error from a `Result<_, E>` is wrapped into
`Error::EvalError`.

### Command Line Tools

#### Interactive REPL (a demo is also available)
```bash
cargo run --example repl --features="scheme jsonlogic"
```


## Supported Operations

### Arithmetic
- `+`, `-`, `*`: Basic arithmetic with overflow detection
- Supports variadic operations: `(+ 1 2 3 4)` or `{"+": [1,2,3,4]}`

### Comparisons
- `===`, `!==`: Strict equality (no type coercion)
- `>`, `<`, `>=`, `<=`: Numeric comparisons with chaining

### Boolean Logic
- `and`, `or`: Short-circuiting logical operations
- `not` (`!`): Logical negation

### String Operations
- `string-append` (`cat`): String concatenation

### List Operations
- `list`: Create lists from arguments
- `car`, `cdr`: List access (first element, rest of list)

### Control Flow
- `if`: Three-argument conditional (`if condition then else`)

### Utilities
- `max`, `min`: Find maximum/minimum values
- `quote`: Return literal data without evaluation

## Error Handling

RulesXP enforces strict error handling:

```jsonc
// Type mismatches are errors
{"===": [1, "1"]}        // Error: Cannot compare number and string
{"and": [1, true]}       // Error: Expected boolean, got number

// Arity errors caught at parse time
{"if": [true]}           // Error: 'if' requires exactly 3 arguments
{"not": []}              // Error: 'not' requires exactly 1 argument
...
```

### As a Library
```rust
use rulesxp::{jsonlogic::parse_jsonlogic, scheme::parse_scheme, evaluator::*};

let mut env = evaluator::create_global_env();
let expr = scheme::parse_scheme("(+ 1 2 3)").unwrap();
let result = evaluator::eval(&expr, &mut env).unwrap();
println!("{}", result); // 6
```

## Current Status

### Implemented
- [x] JSONLogic and Scheme parsers
- [x] Core arithmetic, boolean, and comparison operations
- [x] String operations and list construction
- [x] Error handling with clear messages
- [x] Interactive REPL with dual-language support

### Future Plans
- [ ] Additional language syntax support
- [ ] Stabilized Rust API
- [ ] ABI for FFI from C++/C#

## Contributing

This project welcomes contributions and suggestions.  Most contributions require you to agree to a
Contributor License Agreement (CLA) declaring that you have the right to, and actually do, grant us
the rights to use your contribution. For details, visit [Contributor License Agreements](https://cla.opensource.microsoft.com).

When you submit a pull request, a CLA bot will automatically determine whether you need to provide
a CLA and decorate the PR appropriately (e.g., status check, comment). Simply follow the instructions
provided by the bot. You will only need to do this once across all repos using our CLA.

This project has adopted the [Microsoft Open Source Code of Conduct](https://opensource.microsoft.com/codeofconduct/).
For more information see the [Code of Conduct FAQ](https://opensource.microsoft.com/codeofconduct/faq/) or
contact [opencode@microsoft.com](mailto:opencode@microsoft.com) with any additional questions or comments.

## Trademarks

This project may contain trademarks or logos for projects, products, or services. Authorized use of Microsoft
trademarks or logos is subject to and must follow
[Microsoft's Trademark & Brand Guidelines](https://www.microsoft.com/legal/intellectualproperty/trademarks/usage/general).
Use of Microsoft trademarks or logos in modified versions of this project must not cause confusion or imply Microsoft sponsorship.
Any use of third-party trademarks or logos are subject to those third-party's policies.

## Repository

* <https://github.com/microsoft/rulesxp>

