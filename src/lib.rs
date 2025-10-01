//! RulesXP - Multi-language rules expression evaluator.
//!
//! This crate provides a minimalistic expression evaluator that supports both Scheme syntax
//! and JSONLogic operations with strict typing. It implements a proper subset of both
//! languages designed for reliable rule evaluation with predictable behavior.
//!
//! ## Dual Language Support
//!
//! The evaluator accepts expressions in Scheme syntax but can evaluate operations that map
//! to both Scheme and JSONLogic semantics:
//!
//! ```scheme
//! ;; Scheme syntax
//! (+ 1 2 3)           ; arithmetic
//! (if #t "yes" "no")  ; conditionals  
//! (and #t #f)         ; boolean logic
//! (car '(1 2 3))      ; list operations
//! ```
//!
//! The same operations can be represented in JSONLogic:
//! ```json
//! {"+": [1, 2, 3]}
//! {"if": [true, "yes", "no"]}  
//! {"and": [true, false]}
//! {"car": [[1, 2, 3]]}
//! ```
//!
//! ## Strict Typing
//!
//! This interpreter implements stricter semantics than standard Scheme or JSONLogic:
//! - No type coercion (numbers don't become strings, etc.)
//! - Boolean operations require actual boolean values (no "truthiness")
//! - Arithmetic overflow detection and error reporting
//! - Strict arity checking for all functions
//!
//! Any program accepted by this interpreter will give identical results in standard
//! Scheme R7RS-small or JSONLogic interpreters, but the converse is not true due to
//! our additional type safety requirements.
//!
//! ## Modules
//!
//! - `scheme`: S-expression parsing from text
//! - `evaluator`: Core expression evaluation engine  
//! - `builtinops`: Built-in operations with dual-language mapping
//! - `jsonlogic`: JSONLogic format conversion and integration

use std::fmt;

/// Maximum parsing depth to prevent stack overflow attacks
/// This limits deeply nested structures in both S-expression and JSONLogic parsers
pub const MAX_PARSE_DEPTH: usize = 32;

/// Maximum evaluation depth to prevent stack overflow in recursive evaluation
/// This limits deeply nested function calls and expressions during evaluation
/// Set higher than parse depth to allow for nested function applications
pub const MAX_EVAL_DEPTH: usize = 64;

/// Error types for the interpreter
#[derive(Debug, Clone, PartialEq)]
pub enum SchemeError {
    ParseError(String),
    EvalError(String),
    TypeError(String),
    UnboundVariable(String),
    ArityError {
        expected: usize,
        got: usize,
        expression: Option<String>, // Optional expression context
    },
}

impl SchemeError {
    /// Create an ArityError without expression context
    pub fn arity_error(expected: usize, got: usize) -> Self {
        SchemeError::ArityError {
            expected,
            got,
            expression: None,
        }
    }

    /// Create an ArityError with expression context
    pub fn arity_error_with_expr(expected: usize, got: usize, expression: String) -> Self {
        SchemeError::ArityError {
            expected,
            got,
            expression: Some(expression),
        }
    }
}

impl fmt::Display for SchemeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            SchemeError::ParseError(msg) => write!(f, "Parse error: {}", msg),
            SchemeError::EvalError(msg) => write!(f, "Evaluation error: {}", msg),
            SchemeError::TypeError(msg) => write!(f, "Type error: {}", msg),
            SchemeError::UnboundVariable(var) => write!(f, "Unbound variable: {}", var),
            SchemeError::ArityError {
                expected,
                got,
                expression,
            } => match expression {
                Some(expr) => write!(
                    f,
                    "Arity error in expression {}: expected {} arguments, got {}",
                    expr, expected, got
                ),
                None => write!(
                    f,
                    "Arity error: expected {} arguments, got {}",
                    expected, got
                ),
            },
        }
    }
}

pub mod ast;
pub mod builtinops;
pub mod evaluator;

#[cfg(feature = "jsonlogic")]
pub mod jsonlogic;

#[cfg(feature = "scheme")]
pub mod scheme;
