# Mini Scheme Interpreter

A minimal Scheme-compatible interpreter implemented in Rust, built for simplicity.

## Features

### Data Types
- **Numbers**: Floating-point numbers (`42`, `3.14`, `-5`)
- **Booleans**: `#t` (true) and `#f` (false)
- **Strings**: `"hello world"`
- **Symbols**: Identifiers like `foo`, `+`, `>=`
- **Lists**: `(1 2 3)`, including nested lists
- **Nil**: Empty list `()`
- **Functions**: Both built-in and user-defined lambda functions

### Special Forms
- **`quote`**: Return literal data without evaluation
  ```scheme
  (quote hello)       ; => hello
  (quote (1 2 3))     ; => (1 2 3)
  ```

- **`define`**: Define variables and functions
  ```scheme
  (define x 42)
  (define square (lambda (x) (* x x)))
  ```

- **`if`**: Conditional expressions
  ```scheme
  (if #t 1 2)         ; => 1
  (if #f 1 2)         ; => 2
  (if #t 1)           ; => 1
  (if #f 1)           ; => ()
  ```

- **`lambda`**: Create anonymous functions
  ```scheme
  (lambda (x) (* x x))
  ((lambda (x y) (+ x y)) 3 4)  ; => 7
  ```

### Built-in Functions

#### Arithmetic
- **`+`**: Addition (`(+ 1 2 3)` => `6`)
- **`-`**: Subtraction (`(- 10 3 2)` => `5`, `(- 5)` => `-5`)
- **`*`**: Multiplication (`(* 2 3 4)` => `24`)

#### Comparison
- **`=`**: Equality (`(= 5 5)` => `#t`)
- **`<`**: Less than (`(< 3 5)` => `#t`)
- **`>`**: Greater than (`(> 5 3)` => `#t`)
- **`<=`**: Less than or equal (`(<= 5 5)` => `#t`)
- **`>=`**: Greater than or equal (`(>= 5 3)` => `#t`)

#### List Operations
- **`car`**: First element of list (`(car (list 1 2 3))` => `1`)
- **`cdr`**: Rest of list (`(cdr (list 1 2 3))` => `(2 3)`)
- **`cons`**: Add element to front (`(cons 0 (list 1 2))` => `(0 1 2)`)
- **`list`**: Create list (`(list 1 2 3)` => `(1 2 3)`)
- **`null?`**: Check if empty (`(null? ())` => `#t`)

## Usage

### REPL (Interactive Mode)
```bash
cargo run --bin repl
```

This starts an interactive Read-Eval-Print Loop where you can type Scheme expressions:

```
Mini Scheme Interpreter v0.1.0
Type expressions to evaluate them, or Ctrl+C to exit.

scheme> (+ 1 2 3)
6
scheme> (define square (lambda (x) (* x x)))
square
scheme> (square 5)
25
scheme> :help
Mini Scheme Interpreter Commands:
  :help    - Show this help message
  :env     - Show current environment bindings
  :quit    - Exit the interpreter
  :exit    - Exit the interpreter
...
```

### As a Library
```rust
use sexpr::{parser, evaluator, Environment};

let mut env = evaluator::create_global_env();
let expr = parser::parse("(+ 1 2 3)").unwrap();
let result = evaluator::eval(&expr, &mut env).unwrap();
println!("{}", result); // 6
```

## Examples

### Basic Arithmetic
```scheme
scheme> (+ 10 (* 3 4) (- 8 3))
27

scheme> (* (+ 2 3) (- 7 2))
25
```

### Variable Definition and Usage
```scheme
scheme> (define radius 5)
radius
scheme> (* radius radius)
25
```

### Function Definition
```scheme
scheme> (define abs (lambda (x) (if (< x 0) (- x) x)))
abs
scheme> (abs -5)
5
scheme> (abs 3)
3
```

### Higher-Order Functions
```scheme
scheme> (define twice (lambda (f x) (f (f x))))
twice
scheme> (define inc (lambda (x) (+ x 1)))
inc
scheme> (twice inc 5)
7
```

### List Processing
```scheme
scheme> (define my-list (list 1 2 3 4 5))
my-list
scheme> (car my-list)
1
scheme> (cdr my-list)
(2 3 4 5)
scheme> (cons 0 my-list)
(0 1 2 3 4 5)
```

### Lexical Scoping
```scheme
scheme> (define make-adder (lambda (n) (lambda (x) (+ x n))))
make-adder
scheme> (define add5 (make-adder 5))
add5
scheme> (add5 10)
15
```

## Architecture

The interpreter is built with three main components:

1. **Parser** (`src/parser.rs`): Uses the `nom` parsing library to convert text into S-expressions
2. **Evaluator** (`src/evaluator.rs`): Evaluates S-expressions in environments with proper lexical scoping
3. **REPL** (`src/bin/repl.rs`): Interactive shell using `rustyline` for command history and editing

### Core Types
- `Value`: Enum representing all possible Scheme values
- `Environment`: Hash map-based environment for variable bindings with parent chain for scoping
- `SchemeError`: Comprehensive error types for parsing and evaluation errors

## Limitations

This is a **minimal** Scheme interpreter focused on simplicity. It does **not** include:

- Recursive function definitions (requires `letrec` semantics)
- Macros or syntax transformation
- Continuations (`call/cc`)
- Tail call optimization
- Garbage collection beyond Rust's automatic memory management
- Module system
- Advanced numeric types (rationals, complex numbers)
- Full R7RS compliance

