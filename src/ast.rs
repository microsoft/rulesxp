use crate::builtinops::BuiltinOp;
use crate::SchemeError;

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
    /// Pre-compiled operations with their arguments (optimized during parsing)
    PrecompiledOp {
        op: &'static BuiltinOp,
        op_name: String,
        args: Vec<Value>,
    },
    /// Built-in functions (used when called through Symbol, not pre-optimized due to dynamism)
    BuiltinFunction(fn(&[Value]) -> Result<Value, SchemeError>),
    /// User-defined functions (params, body, closure env)
    Function {
        params: Vec<String>,
        body: Box<Value>,
        env: crate::evaluator::Environment,
    },
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
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
            Value::PrecompiledOp { .. } => {
                // Display PrecompiledOp as parseable list form for round-trip compatibility
                write!(f, "{}", self.to_uncompiled_form())
            },
            Value::Function { .. } => write!(f, "#<function>"),
        }
    }
}

impl Value {
    /// Convert PrecompiledOp back to List form for display purposes
    pub fn to_uncompiled_form(&self) -> Value {
        match self {
            Value::PrecompiledOp { op_name, args, .. } => {
                let mut elements = vec![Value::Symbol(op_name.clone())];
                for arg in args {
                    elements.push(arg.to_uncompiled_form()); // Recursively convert nested PrecompiledOps
                }
                Value::List(elements)
            }
            Value::List(elements) => {
                // Recursively convert nested elements
                Value::List(elements.iter().map(|elem| elem.to_uncompiled_form()).collect())
            }
            other => other.clone(), // Leave other types unchanged
        }
    }

    /// Check if a value represents nil (empty list)
    pub fn is_nil(&self) -> bool {
        matches!(self, Value::List(list) if list.is_empty())
    }
}
