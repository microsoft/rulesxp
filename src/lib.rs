//! S-expression interpreter with dual Scheme and JSONLogic support.
//! 
//! This crate provides a minimalistic expression evaluator that supports both Scheme syntax 
//! and JSONLogic operations. It implements a proper subset of both languages with stronger 
//! typing guarantees than either parent language.
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
//! - `parser`: S-expression parsing from text
//! - `evaluator`: Core expression evaluation engine  
//! - `builtinops`: Built-in operations with dual-language mapping
//! - `jsonlogic`: JSONLogic format conversion and integration

use std::fmt;

/// Error types for the interpreter
#[derive(Debug, Clone, PartialEq)]
pub enum SchemeError {
    ParseError(String),
    EvalError(String),
    TypeError(String),
    UnboundVariable(String),
    ArityError { expected: usize, got: usize },
}

impl std::error::Error for SchemeError {}

impl fmt::Display for SchemeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            SchemeError::ParseError(msg) => write!(f, "Parse error: {}", msg),
            SchemeError::EvalError(msg) => write!(f, "Evaluation error: {}", msg),
            SchemeError::TypeError(msg) => write!(f, "Type error: {}", msg),
            SchemeError::UnboundVariable(var) => write!(f, "Unbound variable: {}", var),
            SchemeError::ArityError { expected, got } => {
                write!(
                    f,
                    "Arity error: expected {} arguments, got {}",
                    expected, got
                )
            }
        }
    }
}

pub mod ast;
pub mod builtinops;
pub mod evaluator;
pub mod jsonlogic;
pub mod parser;

// Core types and parsing
pub use ast::Value;
pub use parser::parse;

// Evaluation engine  
pub use evaluator::{eval, Environment, create_global_env};

// Built-in operations with dual-language support
pub use builtinops::{
    map_jsonlogic_id_to_scheme, map_scheme_id_to_jsonlogic,
    BUILTIN_OPS, BUILTIN_OPS_JSONLOGIC
};

// JSONLogic integration
pub use jsonlogic::{parse_jsonlogic, value_to_jsonlogic};
