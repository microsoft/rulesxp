/// This module defines the core Abstract Syntax Tree (AST) types and helper functions
/// for representing Scheme values in the interpreter. The main enum, [`Value`], covers
/// all Scheme data types, including numbers, symbols, strings, booleans, lists, built-in
/// and user-defined functions, and precompiled operations. Ergonomic helper functions
/// such as [`val`], [`sym`], and [`nil`] are provided for convenient AST construction
/// in both code and tests. The module also implements conversion traits for common Rust
/// types, making it easy to build Scheme values from Rust literals, arrays, slices, and
/// vectors. Equality and display logic are customized to match Scheme semantics, including
/// round-trip compatibility for precompiled operations.
use crate::SchemeError;
use crate::builtinops::BuiltinOp;

/// Allowed non-alphanumeric characters in Scheme symbol names
pub const SYMBOL_SPECIAL_CHARS: &str = "+-*/<>=!?_";

/// Check if a string is a valid Scheme symbol name
/// Valid: non-empty, no leading digit, no "-digit" prefix, alphanumeric + SYMBOL_SPECIAL_CHARS
/// Note: This function is tested as part of the parser tests in parser.rs
pub(crate) fn is_valid_symbol(name: &str) -> bool {
    if name.is_empty() {
        return false;
    }

    let mut chars = name.chars();
    let first_char = chars.next().unwrap();

    // Check first character restrictions
    if first_char.is_ascii_digit() {
        return false;
    }

    if first_char == '-'
        && let Some(second_char) = chars.next()
        && second_char.is_ascii_digit()
    {
        return false;
    }

    // Check all characters are valid
    name.chars()
        .all(|c| c.is_alphanumeric() || SYMBOL_SPECIAL_CHARS.contains(c))
}

/// Core AST type in our Scheme interpreter
///
/// Note: PrecompiledOps (optimized s-expressions) don't equality-compare to dynamically
/// generated unoptimized s-expressions. However, since no expression can *return* a
/// PrecompiledOp (they're consumed during evaluation), this is not a concern for user code.
///
/// To build an AST, use the ergonomic helper functions:
/// - `val(42)` for values, `sym("name")` for symbols, `nil()` for empty lists
/// - `val([1, 2, 3])` for homogeneous lists
/// - `val(vec![sym("op"), val(42)])` for mixed lists
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
    /// Unspecified values (e.g., return value of define)
    /// These values never equal themselves or any other value
    Unspecified,
}

// From trait implementations for Value - enables .into() conversion
impl From<&str> for Value {
    fn from(s: &str) -> Self {
        Value::String(s.to_string())
    }
}

impl From<String> for Value {
    fn from(s: String) -> Self {
        Value::String(s)
    }
}

impl From<bool> for Value {
    fn from(b: bool) -> Self {
        Value::Bool(b)
    }
}

macro_rules! impl_from_integer {
    ($int_type:ty) => {
        impl From<$int_type> for Value {
            fn from(n: $int_type) -> Self {
                Value::Number(n as i64)
            }
        }
    };
}

// Generate From implementations for all integer types
impl_from_integer!(i8);
impl_from_integer!(i16);
impl_from_integer!(i32);
impl_from_integer!(i64); // Special case - no casting
impl_from_integer!(u8);
impl_from_integer!(u16);
impl_from_integer!(u32);

impl<T: Into<Value>> From<Vec<T>> for Value {
    fn from(v: Vec<T>) -> Self {
        Value::List(v.into_iter().map(|x| x.into()).collect())
    }
}

impl<T: Into<Value>, const N: usize> From<[T; N]> for Value {
    fn from(arr: [T; N]) -> Self {
        Value::List(arr.into_iter().map(|x| x.into()).collect())
    }
}

impl<T: Into<Value> + Clone> From<&[T]> for Value {
    fn from(slice: &[T]) -> Self {
        Value::List(slice.iter().cloned().map(|x| x.into()).collect())
    }
}

///   Helper function for creating symbols - works great in mixed lists!
///   Accepts both &str and String via Into<&str>
pub(crate) fn sym<S: AsRef<str>>(name: S) -> Value {
    Value::Symbol(name.as_ref().to_string())
}

/// Helper function for creating Values - works great in mixed lists!
/// Accepts any type that can be converted to Value
pub(crate) fn val<T: Into<Value>>(value: T) -> Value {
    value.into()
}

/// Helper function for creating empty lists (nil) - follows Lisp/Scheme conventions
/// In Lisp, nil represents the empty list
pub(crate) fn nil() -> Value {
    Value::List(vec![])
}

/// Helper function for creating unspecified values
/// These are returned by operations like define that have no meaningful return value
pub(crate) fn unspecified() -> Value {
    Value::Unspecified
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Number(n) => write!(f, "{}", n),
            Value::Symbol(s) => write!(f, "{}", s),
            Value::String(s) => {
                write!(f, "\"")?;
                for ch in s.chars() {
                    match ch {
                        '"' => write!(f, "\\\"")?,
                        '\\' => write!(f, "\\\\")?,
                        '\n' => write!(f, "\\n")?,
                        '\t' => write!(f, "\\t")?,
                        '\r' => write!(f, "\\r")?,
                        c => write!(f, "{}", c)?,
                    }
                }
                write!(f, "\"")
            }
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
            Value::Unspecified => write!(f, "#<unspecified>"),
        }
    }
}

impl Value {
    /// Convert PrecompiledOp back to List form for display purposes
    pub(crate) fn to_uncompiled_form(&self) -> Value {
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
    pub(crate) fn is_nil(&self) -> bool {
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
            (Value::Unspecified, _) => false, // Unspecified never equals anything
            (_, Value::Unspecified) => false, // Nothing equals Unspecified
            _ => false,                       // Different variants are never equal
        }
    }
}

#[cfg(test)]
mod helper_function_tests {
    use super::*;

    #[test]
    fn test_helper_functions_data_driven() {
        // Test cases as (Value, Value) tuples: (helper_result, expected_value)
        let test_cases = vec![
            // Basic numbers
            (val(42), Value::Number(42)),
            (val(-17), Value::Number(-17)),
            (val(-0), Value::Number(0)),
            // Different integer types from macro
            (val(4294967295u32), Value::Number(4294967295)),
            (val(2147483647i32), Value::Number(2147483647)),
            (val(255u8), Value::Number(255)),
            (val(-128i8), Value::Number(-128)),
            (val(65535u16), Value::Number(65535)),
            (val(-32768i16), Value::Number(-32768)),
            (
                val(9223372036854775807i64),
                Value::Number(9223372036854775807),
            ),
            (val(i64::MIN), Value::Number(i64::MIN)),
            // Basic booleans
            (val(true), Value::Bool(true)),
            (val("hello"), Value::String("hello".to_string())),
            (val(""), Value::String("".to_string())),
            // Sym, from both &str and String
            (sym("foo-bar?"), Value::Symbol("foo-bar?".to_string())),
            (sym("-"), Value::Symbol("-".to_string())),
            (sym(String::from("test")), Value::Symbol("test".to_string())),
            // Empty list (nil)
            (nil(), Value::List(vec![])),
            // Lists from arrays and vecs of primitives
            (
                val([1, 2, 3]),
                Value::List(vec![Value::Number(1), Value::Number(2), Value::Number(3)]),
            ),
            (
                val(["hello", "world"]),
                Value::List(vec![
                    Value::String("hello".to_string()),
                    Value::String("world".to_string()),
                ]),
            ),
            (
                val([true, false, true]),
                Value::List(vec![
                    Value::Bool(true),
                    Value::Bool(false),
                    Value::Bool(true),
                ]),
            ),
            // Mixed type lists using helper functions
            (
                val(vec![sym("operation"), val(42), val("result"), val(true)]),
                Value::List(vec![
                    Value::Symbol("operation".to_string()),
                    Value::Number(42),
                    Value::String("result".to_string()),
                    Value::Bool(true),
                ]),
            ),
        ];

        run_helper_function_tests(test_cases);
    }

    /// Helper function to run data-driven tests for helper functions
    fn run_helper_function_tests(test_cases: Vec<(Value, Value)>) {
        for (i, (actual, expected)) in test_cases.iter().enumerate() {
            if actual != expected {
                panic!(
                    "Test case {} failed:\n  Expected: {:?}\n  Got: {:?}",
                    i + 1,
                    expected,
                    actual
                );
            }
        }
    }

    #[test]
    fn test_unspecified_values() {
        // Unspecified never equals anything, including itself
        let unspec = Value::Unspecified;
        assert_ne!(unspec, unspec);
        assert_ne!(unspec, Value::Unspecified);
        assert_ne!(unspec, val(42));
    }
}
