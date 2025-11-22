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

### Registering Custom Builtins

You can extend the evaluator with your own builtins using strongly-typed
Rust functions. These are registered as **builtin operations** on the
`Environment`.

#### Fixed-arity builtins

```rust
use rulesxp::{Error, ast::Value, evaluator};

// Infallible builtin: returns a bare i64
fn add2(a: i64, b: i64) -> i64 {
    a + b
}

// Fallible builtin: returns Result<T, Error>
fn safe_div(a: i64, b: i64) -> Result<i64, Error> {
    if b == 0 {
        Err(Error::EvalError("division by zero".into()))
    } else {
        Ok(a / b)
    }
}

let mut env = evaluator::create_global_env();
env.register_builtin_operation::<(i64, i64)>("add2", add2);
env.register_builtin_operation::<(i64, i64)>("safe-div", safe_div);

// Now you can call (add2 7 5) or (safe-div 6 3) from Scheme
// Or you can call {"add2" : [7, 5]} or {"safe-div" : [6, 3]} from JSONLogic
```

#### List and variadic builtins

For list-style and variadic behavior, use the iterator-based
parameter types from `rulesxp::evaluator`.

```rust
use rulesxp::{Error, ast::Value, evaluator};
use rulesxp::builtinops::Arity;
use rulesxp::evaluator::{NumIter, ValueIter};

// Single list argument: (sum-list (list 1 2 3 4)) => 10
fn sum_list(nums: NumIter<'_>) -> i64 {
    nums.sum()
}

// Variadic over all arguments: (count-numbers 1 "x" 2 #t 3) => 3
fn count_numbers(args: ValueIter<'_>) -> i64 {
    args.filter(|v| matches!(v, Value::Number(_))).count() as i64
}

let mut env = evaluator::create_global_env();

// List parameter from a single list argument
env.register_builtin_operation::<(NumIter<'static>,)>("sum-list", sum_list);

// Variadic builtin with explicit arity metadata
env.register_variadic_builtin_operation::<(ValueIter<'static>,)>(
    "count-numbers",
    Arity::AtLeast(0),
    count_numbers,
);
```

The typed registration APIs currently support:

- **Parameter types** (as elements of the `Args` tuple):
  - `i64` (number)
  - `bool` (boolean)
  - `&str` (borrowed string slices)
  - `Value` (owned access to the raw AST value)
  - `ValueIter<'_>` (iterate over `&Value` from a list/rest argument)
  - `NumIter<'_>` (iterate over numeric elements as `i64`)
  - `BoolIter<'_>` (iterate over boolean elements as `bool`)
  - `StringIter<'_>` (iterate over string elements as `&str`)

- **Return types**:
  - `Result<Value, Error>`
  - `Result<T, Error>` where `T: Into<Value>` (for example `i64`,
    `bool`, `&str`, arrays/vectors of those types, or `Vec<Value>`)
  - bare `T` where `T: Into<Value>` (for infallible helpers, which are
    automatically wrapped as `Ok(T)`)

Arity is enforced automatically. Conversion errors yield `TypeError`,
and builtin errors are surfaced directly as `Error` values.

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

