use crate::SchemeError;
use crate::builtinops::BuiltinOp;

/// Core AST value types in our Scheme interpreter
///
/// Note: PrecompiledOps (optimized s-expressions) don't equality-compare to dynamically
/// generated unoptimized s-expressions. However, since no expression can *return* a
/// PrecompiledOp (they're consumed during evaluation), this is not a concern for user code.
#[derive(Debug, Clone)]
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
        op_id: String,
        args: Vec<Value>,
    },
    /// Built-in functions (used when called through Symbol, not pre-optimized due to dynamism)
    /// Uses id string for equality comparison instead of function pointer
    BuiltinFunction {
        id: String,
        func: fn(&[Value]) -> Result<Value, SchemeError>,
    },
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
            Value::BuiltinFunction { id, .. } => write!(f, "#<builtin-function:{}>", id),
            Value::PrecompiledOp { .. } => {
                // Display PrecompiledOp as parseable list form for round-trip compatibility
                write!(f, "{}", self.to_uncompiled_form())
            }
            Value::Function { .. } => write!(f, "#<function>"),
        }
    }
}

impl Value {
    /// Convert PrecompiledOp back to List form for display purposes
    pub fn to_uncompiled_form(&self) -> Value {
        match self {
            Value::PrecompiledOp { op, args, .. } => {
                let mut elements = vec![Value::Symbol(op.scheme_id.to_string())];
                for arg in args {
                    elements.push(arg.to_uncompiled_form()); // Recursively convert nested PrecompiledOps
                }
                Value::List(elements)
            }
            Value::List(elements) => {
                // Recursively convert nested elements
                Value::List(
                    elements
                        .iter()
                        .map(|elem| elem.to_uncompiled_form())
                        .collect(),
                )
            }
            other => other.clone(), // Leave other types unchanged
        }
    }

    /// Check if a value represents nil (empty list)
    pub fn is_nil(&self) -> bool {
        matches!(self, Value::List(list) if list.is_empty())
    }
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Value::Number(a), Value::Number(b)) => a == b,
            (Value::Symbol(a), Value::Symbol(b)) => a == b,
            (Value::String(a), Value::String(b)) => a == b,
            (Value::Bool(a), Value::Bool(b)) => a == b,
            (Value::List(a), Value::List(b)) => a == b,
            (
                Value::PrecompiledOp {
                    op_id: id1,
                    args: args1,
                    ..
                },
                Value::PrecompiledOp {
                    op_id: id2,
                    args: args2,
                    ..
                },
            ) => {
                // Compare PrecompiledOps by id string, not function pointer
                id1 == id2 && args1 == args2
            }
            (Value::BuiltinFunction { id: id1, .. }, Value::BuiltinFunction { id: id2, .. }) => {
                // Compare BuiltinFunctions by id string, not function pointer
                id1 == id2
            }
            (
                Value::Function {
                    params: p1,
                    body: b1,
                    env: e1,
                },
                Value::Function {
                    params: p2,
                    body: b2,
                    env: e2,
                },
            ) => p1 == p2 && b1 == b2 && e1 == e2,
            _ => false, // Different variants are never equal
        }
    }
}
