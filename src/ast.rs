use crate::SchemeError;
use std::fmt;

/// Core value types in our Scheme interpreter
#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    /// Numbers (integers only)
    Number(i64),
    /// Symbols (identifiers)
    Symbol(String),
    /// String literals
    String(String),
    /// Boolean values
    Bool(bool),
    /// Lists (including proper and improper lists, empty list represents nil)
    List(Vec<Value>),
    /// Built-in functions
    BuiltinFunction(fn(&[Value]) -> Result<Value, SchemeError>),
    /// User-defined functions (params, body, closure env)
    Function {
        params: Vec<String>,
        body: Box<Value>,
        env: crate::evaluator::Environment,
    },
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Value::Number(n) => write!(f, "{}", n),
            Value::Symbol(s) => write!(f, "{}", s),
            Value::String(s) => write!(f, "\"{}\"", s),
            Value::Bool(b) => write!(f, "{}", if *b { "#t" } else { "#f" }),
            Value::List(elements) => {
                write!(f, "(")?;
                for (i, elem) in elements.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{}", elem)?;
                }
                write!(f, ")")
            }
            Value::BuiltinFunction(_) => write!(f, "#<builtin-function>"),
            Value::Function { .. } => write!(f, "#<function>"),
        }
    }
}

impl Value {
    /// Check if a value represents nil (empty list)
    pub fn is_nil(&self) -> bool {
        match self {
            Value::List(list) if list.is_empty() => true,
            _ => false,
        }
    }
}
