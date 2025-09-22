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
pub mod evaluator;
pub mod jsonlogic;
pub mod parser;
