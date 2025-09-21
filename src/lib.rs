use std::collections::HashMap;
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
        env: Environment,
    },
}

/// Environment for variable bindings
#[derive(Debug, Clone, PartialEq, Default)]
pub struct Environment {
    bindings: HashMap<String, Value>,
    parent: Option<Box<Environment>>,
}

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

    /// Check if a value is truthy according to strict semantics
    /// Only #f is falsy, everything else (including empty lists) is truthy
    pub fn is_truthy(&self) -> bool {
        match self {
            Value::Bool(false) => false,
            _ => true,
        }
    }

    /// Check if a value is falsy according to Scheme semantics
    /// This is the logical inverse of is_truthy
    pub fn is_falsy(&self) -> bool {
        !self.is_truthy()
    }
}

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

impl Environment {
    pub fn new() -> Self {
        Environment {
            bindings: HashMap::new(),
            parent: None,
        }
    }

    pub fn with_parent(parent: Environment) -> Self {
        Environment {
            bindings: HashMap::new(),
            parent: Some(Box::new(parent)),
        }
    }

    pub fn define(&mut self, name: String, value: Value) {
        self.bindings.insert(name, value);
    }

    pub fn get(&self, name: &str) -> Option<&Value> {
        self.bindings
            .get(name)
            .or_else(|| self.parent.as_ref().and_then(|parent| parent.get(name)))
    }

    pub fn get_mut(&mut self, name: &str) -> Option<&mut Value> {
        self.bindings.get_mut(name)
    }
}

pub mod parser;
pub mod evaluator;
