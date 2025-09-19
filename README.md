# Mini Scheme Interpreter

A minimal Scheme-compatible interpreter implemented in Rust, built for simplicity.

## Features

### Data Types
- **Numbers**: Integer numbers only (`42`, `-5`, `#xFF`, `#x1A`)
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

#### Logic Operations
- **`and`**: Logical AND - requires boolean arguments only
  ```scheme
  (and #t #f)         ; => #f
  (and #t #t)         ; => #t  
  (and)               ; => #t
  (and 1 2)           ; => Error: and requires boolean arguments
  ```
- **`or`**: Logical OR - requires boolean arguments only
  ```scheme
  (or #f #t)          ; => #t
  (or #f #f)          ; => #f
  (or)                ; => #f
  (or 1 2)            ; => Error: or requires boolean arguments
  ```
- **`not`**: Logical NOT - requires boolean argument only
  ```scheme
  (not #t)            ; => #f
  (not #f)            ; => #t
  (not 42)            ; => Error: not requires a boolean argument
  ```

#### General Equality
- **`equal?`**: Structural equality for all types (`(equal? "hello" "hello")` => `#t`)

#### Error Handling
- **`error`**: Raise an error with custom message
  ```scheme
  (error "Something went wrong")           ; Raises error with message
  (error "Code:" 404 "not found")         ; Multiple arguments
  ```

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

## Differences from Standard Scheme

This implementation is **stricter** than standard Scheme in several ways:

### 1. Integer-Only Arithmetic
- **Standard Scheme**: Supports integers, rationals, reals, and complex numbers
- **This Implementation**: Only supports 64-bit signed integers (`i64`)
- **Impact**: No floating-point arithmetic, division operator removed to avoid precision issues
  ```scheme
  ; Standard Scheme
  (+ 1.5 2.3)         ; => 3.8
  (/ 7 3)             ; => 7/3 or 2.333...
  
  ; This Implementation  
  (+ 1 2)             ; => 3 (integers only)
  (/ 7 3)             ; Error: / not implemented
  ```

### 2. Strict Boolean Logic Operations
- **Standard Scheme**: `and`, `or`, `not`, `if` use truthy/falsy semantics (only `#f` and `()` are false)
- **This Implementation**: Requires actual boolean values (`#t` or `#f`) for all boolean operations
- **Impact**: Must explicitly convert values to booleans, more predictable control flow
  ```scheme
  ; Standard Scheme
  (and 1 2 3)         ; => 3 (returns last truthy value)
  (or #f 42)          ; => 42 (returns first truthy value)
  (not 0)             ; => #f (0 is truthy)
  (if 42 "yes" "no")  ; => "yes" (42 is truthy)
  
  ; This Implementation
  (and #t #t)         ; => #t (booleans only)
  (and 1 2)           ; Error: and requires boolean arguments
  (or #f #t)          ; => #t (booleans only) 
  (not 42)            ; Error: not requires a boolean argument
  (if #t "yes" "no")  ; => "yes" (booleans only)
  (if 42 "yes" "no")  ; Error: if condition must be a boolean
  ```

### 3. Numeric-Only Equality Operator
- **Standard Scheme**: `=` can compare various numeric types
- **This Implementation**: `=` only works on integers, `equal?` for general equality
- **Impact**: Type-safe numeric comparisons, separate general equality
  ```scheme
  ; Standard Scheme
  (= 5 5.0)           ; => #t (numeric equality across types)
  (= "hello" "hello") ; Often an error, but varies
  
  ; This Implementation
  (= 5 5)             ; => #t (integers only)
  (= "hello" "hello") ; Error: = requires numbers
  (equal? "hello" "hello") ; => #t (use equal? for general equality)
  ```

### 4. Fixed Arity for Logic Operations
- **Standard Scheme**: `and` and `or` can take any number of arguments (including zero)
- **This Implementation**: Supports zero or more arguments, but all must be booleans
- **Impact**: More predictable behavior, explicit boolean requirements
  ```scheme
  ; Both Standard Scheme and This Implementation
  (and)               ; => #t
  (or)                ; => #f
  
  ; Difference in argument types
  (and #t 5 "hello")  ; Standard: => "hello", This: Error
  ```

### 5. Hexadecimal Integer Literals
- **Standard Scheme**: Supports various numeric formats including hex (`#x1A`)
- **This Implementation**: Supports decimal and hexadecimal integers
- **Enhancement**: Added hexadecimal support (`#xFF`, `#x1A`) for integer literals

### Benefits of Stricter Design
- **Type Safety**: Catches type mismatches early at evaluation time
- **Predictability**: No ambiguity about implicit type conversions
- **Explicit Intent**: Forces developers to be clear about type expectations
- **Educational Value**: Makes type system concepts more visible
- **Reduced Complexity**: Simpler semantics with fewer edge cases

## Limitations and Design Choices

This is a **minimal** Scheme interpreter with intentionally **stricter semantics** than standard Scheme. 

### Intentionally Stricter (Design Choices)
- **Integer-only arithmetic**: Avoids floating-point precision issues
- **Boolean-only logic operations**: Prevents implicit type conversions  
- **Numeric-only `=` operator**: Type-safe equality checking
- **Explicit type requirements**: Forces clear intent in code

### Not Implemented (Complexity Reduction)
- Recursive function definitions (requires `letrec` semantics)
- Macros or syntax transformation
- Continuations (`call/cc`)
- Tail call optimization
- Garbage collection beyond Rust's automatic memory management
- Module system
- Advanced numeric types (rationals, complex numbers)
- Quote syntax sugar (`'x` for `(quote x)`)
- Full R7RS compliance

