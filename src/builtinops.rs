//! Built-in operations registry with dual Scheme/JSONLogic support.
//!
//! This module provides a unified registry of built-in operations that can be accessed
//! through both Scheme and JSONLogic syntax, with strict typing and error handling.
//!
//! ## Dual Language Support
//!
//! Operations are defined once but accessible through both languages:
//!
//! ```scheme
//! ;; Scheme syntax
//! (not #t)           ; logical negation
//! (+ 1 2 3)          ; arithmetic  
//! (equal? "a" "b")   ; equality test
//! ```
//!
//! ```json
//! // JSONLogic equivalents
//! {"!": [true]}
//! {"+": [1, 2, 3]}
//! {"==": ["a", "b"]}
//! ```
//!
//! ## Functions vs Special Forms
//!
//! - **Functions**: Evaluate all arguments before application (e.g., `+`, `not`, `car`)
//! - **Special Forms**: Control evaluation of arguments (e.g., `if`, `and`, `or`)
//!   
//! Special forms are handled directly by the evaluator and are not in this registry.
//!
//! ## Error Handling
//!
//! This implementation enforces stricter error handling than standard Scheme or JSONLogic:
//!
//! - **Type Safety**: Operations reject incorrect types (e.g., `(not 42)` errors)
//! - **No Coercion**: Numbers don't become strings, no "truthiness" conversions
//! - **Overflow Detection**: Arithmetic operations detect and report overflow
//! - **Arity Checking**: Strict argument count validation for all functions
//!
//! These restrictions ensure predictable behavior and catch errors early.
//!
//! ## Adding New Operations
//!
//! To add a new built-in operation:
//!
//! 1. **Implement the function** following the signature `fn(args: &[Value]) -> Result<Value, SchemeError>`
//! 2. **Add to BUILTIN_OPS** with Scheme identifier and arity
//! 3. **Add to BUILTIN_OPS_JSONLOGIC** if it has a different JSONLogic identifier
//! 4. **Update evaluator** if it's a special form requiring custom evaluation logic
//! 5. **Add comprehensive tests** covering edge cases and error conditions

use crate::SchemeError;
use crate::ast::Value;
use crate::evaluator::{
    Environment, eval_and, eval_define, eval_if, eval_lambda, eval_or, eval_quote,
};
use std::collections::HashMap;
use std::sync::LazyLock;

/// Represents the expected number of arguments for an operation
#[derive(Debug, Clone, PartialEq)]
pub enum Arity {
    /// Exactly n arguments required
    Exact(usize),
    /// At least n arguments required
    AtLeast(usize),
    /// Between min and max arguments (inclusive)
    Range(usize, usize),
    /// Any number of arguments (0 or more)
    Any,
}

impl Arity {
    /// Check if the given number of arguments is valid for this arity constraint
    pub fn validate(&self, arg_count: usize) -> Result<(), SchemeError> {
        let valid = match self {
            Arity::Exact(n) => arg_count == *n,
            Arity::AtLeast(n) => arg_count >= *n,
            Arity::Range(min, max) => arg_count >= *min && arg_count <= *max,
            Arity::Any => true,
        };

        if valid {
            Ok(())
        } else {
            Err(SchemeError::ArityError {
                expected: match self {
                    Arity::Exact(n) => *n,
                    Arity::AtLeast(n) => *n,
                    Arity::Range(min, _) => *min,
                    Arity::Any => 0,
                },
                got: arg_count,
                expression: None, // Builtin validation doesn't have expression context
            })
        }
    }
}

/// Represents the implementation of a built-in expression (function or special form)
#[derive(Clone)]
pub enum OpKind {
    /// Regular function that takes arguments and returns a value
    Function(fn(&[Value]) -> Result<Value, SchemeError>),
    /// Special form that requires access to the environment and unevaluated arguments
    SpecialForm(fn(&[Value], &mut Environment) -> Result<Value, SchemeError>),
}

impl std::fmt::Debug for OpKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OpKind::Function(_) => write!(f, "Function(<fn>)"),
            OpKind::SpecialForm(_) => write!(f, "SpecialForm(<fn>)"),
        }
    }
}

impl PartialEq for OpKind {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (OpKind::Function(f1), OpKind::Function(f2)) => {
                std::ptr::eq(f1 as *const _, f2 as *const _)
            }
            (OpKind::SpecialForm(f1), OpKind::SpecialForm(f2)) => {
                std::ptr::eq(f1 as *const _, f2 as *const _)
            }
            _ => false,
        }
    }
}

/// Definition of a built-in operation
#[derive(Debug, Clone)]
pub struct BuiltinOp {
    /// The Scheme identifier for this operation
    pub scheme_id: &'static str,
    /// The JSONLogic identifier for this operation (may be same as scheme_id)
    pub jsonlogic_id: &'static str,
    /// The implementation of this operation (function or special form)
    pub op_kind: OpKind,
    /// Expected number of arguments
    pub arity: Arity,
}

impl PartialEq for BuiltinOp {
    fn eq(&self, other: &Self) -> bool {
        // Compare operations by their scheme_id, which uniquely identifies them
        self.scheme_id == other.scheme_id
    }
}

impl BuiltinOp {
    /// Check if this operation is a special form
    pub fn is_special_form(&self) -> bool {
        matches!(self.op_kind, OpKind::SpecialForm(_))
    }

    /// Check if the given number of arguments is valid for this operation
    pub fn validate_arity(&self, arg_count: usize) -> Result<(), SchemeError> {
        self.arity.validate(arg_count)
    }
}

//
// Builtin Function Implementations
//

// Macro to generate numeric comparison functions
macro_rules! numeric_comparison {
    ($name:ident, $op:tt, $op_str:expr) => {
        pub fn $name(args: &[Value]) -> Result<Value, SchemeError> {
            // SCHEME-JSONLOGIC-STRICT: Require at least 2 arguments (both standards allow < 2 args but with different semantics)
            if args.len() < 2 {
                return Err(SchemeError::arity_error(2, args.len()));
            }

            // Chain comparisons: all adjacent pairs must satisfy the comparison
            for window in args.windows(2) {
                match window {
                    [Value::Number(a), Value::Number(b)] => {
                        if !(a $op b) {
                            return Ok(Value::Bool(false));
                        }
                    }
                    _ => return Err(SchemeError::TypeError(concat!($op_str, " requires numbers").to_string())),
                }
            }

            Ok(Value::Bool(true))
        }
    };
}

// Generate all comparison functions
numeric_comparison!(builtin_eq, ==, "=");
numeric_comparison!(builtin_lt, <, "<");
numeric_comparison!(builtin_gt, >, ">");
numeric_comparison!(builtin_le, <=, "<=");
numeric_comparison!(builtin_ge, >=, ">=");

pub fn builtin_add(args: &[Value]) -> Result<Value, SchemeError> {
    let mut sum = 0i64;
    for arg in args {
        match arg {
            Value::Number(n) => {
                sum = sum.checked_add(*n).ok_or_else(|| {
                    SchemeError::EvalError("Integer overflow in addition".to_string())
                })?;
            }
            _ => return Err(SchemeError::TypeError("+ requires numbers".to_string())),
        }
    }
    Ok(Value::Number(sum))
}

pub fn builtin_sub(args: &[Value]) -> Result<Value, SchemeError> {
    match args {
        [] => Err(SchemeError::arity_error(1, 0)),
        [Value::Number(first)] => {
            // Unary minus: check for overflow when negating
            let result = first.checked_neg().ok_or_else(|| {
                SchemeError::EvalError("Integer overflow in negation".to_string())
            })?;
            Ok(Value::Number(result))
        }
        [Value::Number(first), rest @ ..] => {
            let mut result = *first;
            for arg in rest {
                match arg {
                    Value::Number(n) => {
                        result = result.checked_sub(*n).ok_or_else(|| {
                            SchemeError::EvalError("Integer overflow in subtraction".to_string())
                        })?;
                    }
                    _ => return Err(SchemeError::TypeError("- requires numbers".to_string())),
                }
            }
            Ok(Value::Number(result))
        }
        _ => Err(SchemeError::TypeError("- requires numbers".to_string())),
    }
}

pub fn builtin_mul(args: &[Value]) -> Result<Value, SchemeError> {
    // SCHEME-STRICT: Require at least 1 argument (Scheme R7RS allows 0 args, returns 1)
    if args.is_empty() {
        return Err(SchemeError::arity_error(1, 0));
    }

    let mut product = 1i64;
    for arg in args {
        match arg {
            Value::Number(n) => {
                product = product.checked_mul(*n).ok_or_else(|| {
                    SchemeError::EvalError("Integer overflow in multiplication".to_string())
                })?;
            }
            _ => return Err(SchemeError::TypeError("* requires numbers".to_string())),
        }
    }
    Ok(Value::Number(product))
}

pub fn builtin_car(args: &[Value]) -> Result<Value, SchemeError> {
    match args {
        [Value::List(list)] => match list.as_slice() {
            [] => Err(SchemeError::EvalError("car of empty list".to_string())),
            [first, ..] => Ok(first.clone()),
        },
        [_] => Err(SchemeError::TypeError("car requires a list".to_string())),
        _ => Err(SchemeError::arity_error(1, args.len())),
    }
}

pub fn builtin_cdr(args: &[Value]) -> Result<Value, SchemeError> {
    match args {
        [Value::List(list)] => match list.as_slice() {
            [] => Err(SchemeError::EvalError("cdr of empty list".to_string())),
            [_, rest @ ..] => Ok(Value::List(rest.to_vec())),
        },
        [_] => Err(SchemeError::TypeError("cdr requires a list".to_string())),
        _ => Err(SchemeError::arity_error(1, args.len())),
    }
}

pub fn builtin_cons(args: &[Value]) -> Result<Value, SchemeError> {
    match args {
        [first, Value::List(rest)] => {
            let mut new_list = vec![first.clone()];
            new_list.extend_from_slice(rest);
            Ok(Value::List(new_list))
        }
        [_, _] => Err(SchemeError::TypeError(
            // SCHEME-STRICT: Require second argument to be a list (Scheme R7RS allows improper lists)
            "cons requires a list as second argument".to_string(),
        )),
        _ => Err(SchemeError::arity_error(2, args.len())),
    }
}

pub fn builtin_list(args: &[Value]) -> Result<Value, SchemeError> {
    Ok(Value::List(args.to_vec()))
}

pub fn builtin_null(args: &[Value]) -> Result<Value, SchemeError> {
    match args {
        [value] => Ok(Value::Bool(value.is_nil())),
        _ => Err(SchemeError::arity_error(1, args.len())),
    }
}

pub fn builtin_not(args: &[Value]) -> Result<Value, SchemeError> {
    match args {
        [Value::Bool(b)] => Ok(Value::Bool(!b)),
        [_] => Err(SchemeError::TypeError(
            "not requires a boolean argument".to_string(),
        )),
        _ => Err(SchemeError::arity_error(1, args.len())),
    }
}

pub fn builtin_equal(args: &[Value]) -> Result<Value, SchemeError> {
    match args {
        [first, second] => {
            // Scheme's equal? is structural equality for all types
            Ok(Value::Bool(first == second))
        }
        _ => Err(SchemeError::arity_error(2, args.len())),
    }
}

pub fn builtin_error(args: &[Value]) -> Result<Value, SchemeError> {
    // Convert a value to error message string
    fn value_to_error_string(value: &Value) -> String {
        match value {
            Value::String(s) => s.clone(), // Remove quotes for error messages
            _ => format!("{}", value),     // Use Display trait for everything else
        }
    }

    // Build multi-part error message
    fn build_error_message(first: &Value, rest: &[Value]) -> String {
        let mut message = value_to_error_string(first);
        for arg in rest {
            message.push(' ');
            message.push_str(&value_to_error_string(arg));
        }
        message
    }

    match args {
        [] => Err(SchemeError::EvalError("Error".to_string())),
        [single] => Err(SchemeError::EvalError(value_to_error_string(single))),
        [first, rest @ ..] => Err(SchemeError::EvalError(build_error_message(first, rest))),
    }
}

/// Global registry of all built-in operations as a simple array
static BUILTIN_OPS: &[BuiltinOp] = &[
    // Arithmetic operations
    BuiltinOp {
        scheme_id: "+",
        jsonlogic_id: "+",
        op_kind: OpKind::Function(builtin_add),
        arity: Arity::AtLeast(0),
    },
    BuiltinOp {
        scheme_id: "-",
        jsonlogic_id: "-",
        op_kind: OpKind::Function(builtin_sub),
        arity: Arity::AtLeast(1),
    },
    BuiltinOp {
        scheme_id: "*",
        jsonlogic_id: "*",
        op_kind: OpKind::Function(builtin_mul),
        arity: Arity::AtLeast(1), // SCHEME-STRICT: Scheme R7RS allows 0 arguments (returns 1)
    },
    // Comparison operations
    BuiltinOp {
        scheme_id: ">",
        jsonlogic_id: ">",
        op_kind: OpKind::Function(builtin_gt),
        arity: Arity::AtLeast(2),
    },
    BuiltinOp {
        scheme_id: ">=",
        jsonlogic_id: ">=",
        op_kind: OpKind::Function(builtin_ge),
        arity: Arity::AtLeast(2),
    },
    BuiltinOp {
        scheme_id: "<",
        jsonlogic_id: "<",
        op_kind: OpKind::Function(builtin_lt),
        arity: Arity::AtLeast(2),
    },
    BuiltinOp {
        scheme_id: "<=",
        jsonlogic_id: "<=",
        op_kind: OpKind::Function(builtin_le),
        arity: Arity::AtLeast(2),
    },
    BuiltinOp {
        scheme_id: "=",
        jsonlogic_id: "scheme-numeric-equals",
        op_kind: OpKind::Function(builtin_eq),
        arity: Arity::AtLeast(2),
    },
    BuiltinOp {
        scheme_id: "equal?",
        jsonlogic_id: "==",
        op_kind: OpKind::Function(builtin_equal),
        arity: Arity::Exact(2),
    },
    // Logical operations
    BuiltinOp {
        scheme_id: "not",
        jsonlogic_id: "!",
        op_kind: OpKind::Function(builtin_not),
        arity: Arity::Exact(1),
    },
    BuiltinOp {
        scheme_id: "and",
        jsonlogic_id: "and",
        op_kind: OpKind::SpecialForm(eval_and),
        arity: Arity::AtLeast(1), // SCHEME-STRICT: Scheme R7RS allows 0 arguments (returns #t)
    },
    BuiltinOp {
        scheme_id: "or",
        jsonlogic_id: "or",
        op_kind: OpKind::SpecialForm(eval_or),
        arity: Arity::AtLeast(1), // SCHEME-STRICT: Scheme R7RS allows 0 arguments (returns #f)
    },
    // Control flow
    BuiltinOp {
        scheme_id: "if",
        jsonlogic_id: "if",
        op_kind: OpKind::SpecialForm(eval_if),
        // SCHEME-JSONLOGIC-STRICT: Require exactly 3 arguments
        // (Scheme allows 2 args with undefined behavior, JSONLogic allows chaining with >3 args)
        arity: Arity::Exact(3),
    },
    // Special forms for language constructs
    BuiltinOp {
        scheme_id: "quote",
        jsonlogic_id: "scheme-quote",
        op_kind: OpKind::SpecialForm(eval_quote),
        arity: Arity::Exact(1),
    },
    BuiltinOp {
        scheme_id: "define",
        jsonlogic_id: "scheme-define",
        op_kind: OpKind::SpecialForm(eval_define),
        arity: Arity::Exact(2),
    },
    BuiltinOp {
        scheme_id: "lambda",
        jsonlogic_id: "scheme-lambda",
        op_kind: OpKind::SpecialForm(eval_lambda),
        // SCHEME-STRICT: Only supports fixed-arity lambdas (lambda (a b c) body)
        // Does not support variadic forms: (lambda args body) or (lambda (a . rest) body)
        // Duplicate parameter names are prohibited per R7RS standard
        arity: Arity::Exact(2),
    },
    // List operations
    BuiltinOp {
        scheme_id: "car",
        jsonlogic_id: "scheme-car",
        op_kind: OpKind::Function(builtin_car),
        arity: Arity::Exact(1),
    },
    BuiltinOp {
        scheme_id: "cdr",
        jsonlogic_id: "scheme-cdr",
        op_kind: OpKind::Function(builtin_cdr),
        arity: Arity::Exact(1),
    },
    BuiltinOp {
        scheme_id: "cons",
        jsonlogic_id: "scheme-cons",
        op_kind: OpKind::Function(builtin_cons),
        arity: Arity::Exact(2),
    },
    BuiltinOp {
        scheme_id: "list",
        jsonlogic_id: "scheme-list",
        op_kind: OpKind::Function(builtin_list),
        arity: Arity::Any,
    },
    BuiltinOp {
        scheme_id: "null?",
        jsonlogic_id: "scheme-null?",
        op_kind: OpKind::Function(builtin_null),
        arity: Arity::Exact(1),
    },
    // Error handling
    BuiltinOp {
        scheme_id: "error",
        jsonlogic_id: "scheme-error",
        op_kind: OpKind::Function(builtin_error),
        arity: Arity::Any,
    },
];

/// Lazy static map from scheme_id to BuiltinOp (private - use find_builtin_op_by_scheme_id)
static BUILTIN_SCHEME: LazyLock<HashMap<&'static str, &'static BuiltinOp>> =
    LazyLock::new(|| BUILTIN_OPS.iter().map(|op| (op.scheme_id, op)).collect());

/// Lazy static map from jsonlogic_id to BuiltinOp (private - use find_builtin_op_by_jsonlogic_id)
static BUILTIN_JSONLOGIC: LazyLock<HashMap<&'static str, &'static BuiltinOp>> =
    LazyLock::new(|| BUILTIN_OPS.iter().map(|op| (op.jsonlogic_id, op)).collect());

/// Get all builtin operations (for internal use by evaluator)
pub fn get_builtin_ops() -> &'static [BuiltinOp] {
    BUILTIN_OPS
}

/// Find a builtin op (with function implementation) by its Scheme id
pub fn find_builtin_op_by_scheme_id(id: &str) -> Option<&'static BuiltinOp> {
    BUILTIN_SCHEME.get(id).copied()
}

/// Find a builtin op (with function implementation) by its JSONLogic id
pub fn find_builtin_op_by_jsonlogic_id(id: &str) -> Option<&'static BuiltinOp> {
    BUILTIN_JSONLOGIC.get(id).copied()
}

/// Get the JSONLogic operator id for a Scheme function
///
/// Uses the global ops registry for consistent mapping.
pub fn map_scheme_id_to_jsonlogic_id(op: &str) -> &str {
    BUILTIN_SCHEME
        .get(op)
        .map(|builtin_op| builtin_op.jsonlogic_id)
        .unwrap_or(op)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_builtin_ops_metadata() {
        // Test that we can find ops by both ids
        let not_op = find_builtin_op_by_scheme_id("not").unwrap();
        assert_eq!(not_op.jsonlogic_id, "!");
        assert_eq!(not_op.arity, Arity::Exact(1));
        assert!(!not_op.is_special_form());

        let not_by_jsonlogic = find_builtin_op_by_jsonlogic_id("!").unwrap();
        // Should be the same operation
        assert!(std::ptr::eq(not_op, not_by_jsonlogic));

        // Test equality mapping
        let equal_op = find_builtin_op_by_scheme_id("equal?").unwrap();
        assert_eq!(equal_op.jsonlogic_id, "==");

        let equal_by_jsonlogic = find_builtin_op_by_jsonlogic_id("==").unwrap();
        // Should be the same operation
        assert!(std::ptr::eq(equal_op, equal_by_jsonlogic));

        // Test special forms
        let and_op = find_builtin_op_by_scheme_id("and").unwrap();
        assert!(and_op.is_special_form());

        let if_op = find_builtin_op_by_scheme_id("if").unwrap();
        assert!(if_op.is_special_form());

        // Test arity validation
        assert_eq!(not_op.arity, Arity::Exact(1));
        assert_eq!(and_op.arity, Arity::AtLeast(1)); // SCHEME-STRICT: Scheme R7RS allows 0 arguments
        assert_eq!(if_op.arity, Arity::Exact(3)); // SCHEME-JSONLOGIC-STRICT: Require exactly 3 arguments
    }

    #[test]
    fn test_builtin_ops_registry() {
        // Test that we can find ops with function implementations
        let add_op = find_builtin_op_by_scheme_id("+").unwrap();
        assert_eq!(add_op.arity, Arity::AtLeast(0));
        assert!(!add_op.is_special_form());

        // Test calling the function
        if let OpKind::Function(func) = &add_op.op_kind {
            let result = func(&[Value::Number(1), Value::Number(2)]).unwrap();
            assert_eq!(result, Value::Number(3));
        } else {
            panic!("Expected Function variant");
        }

        let not_op = find_builtin_op_by_jsonlogic_id("!").unwrap();
        assert_eq!(not_op.jsonlogic_id, "!");

        // Test calling the not function
        if let OpKind::Function(func) = &not_op.op_kind {
            let result = func(&[Value::Bool(true)]).unwrap();
            assert_eq!(result, Value::Bool(false));
        } else {
            panic!("Expected Function variant");
        }

        // Test that special forms are now in the ops registry
        let and_op = find_builtin_op_by_scheme_id("and").unwrap();
        assert!(and_op.is_special_form());

        let or_op = find_builtin_op_by_scheme_id("or").unwrap();
        assert!(or_op.is_special_form());

        let if_op = find_builtin_op_by_scheme_id("if").unwrap();
        assert!(if_op.is_special_form());
    }

    #[test]
    fn test_builtin_function_implementations() {
        // Test arithmetic functions - addition
        assert_eq!(builtin_add(&[]).unwrap(), Value::Number(0)); // Identity
        assert_eq!(builtin_add(&[Value::Number(5)]).unwrap(), Value::Number(5)); // Single number
        assert_eq!(
            builtin_add(&[Value::Number(1), Value::Number(2), Value::Number(3)]).unwrap(),
            Value::Number(6)
        ); // Multiple numbers
        assert_eq!(
            builtin_add(&[Value::Number(-5), Value::Number(10)]).unwrap(),
            Value::Number(5)
        ); // Negative numbers
        assert_eq!(
            builtin_add(&[Value::Number(0), Value::Number(0), Value::Number(0)]).unwrap(),
            Value::Number(0)
        ); // Zeros

        // Test addition error cases
        assert!(builtin_add(&[Value::String("not a number".to_string())]).is_err());
        assert!(builtin_add(&[Value::Number(1), Value::Bool(true)]).is_err());

        // Test arithmetic functions - subtraction
        assert_eq!(builtin_sub(&[Value::Number(5)]).unwrap(), Value::Number(-5)); // Unary minus
        assert_eq!(builtin_sub(&[Value::Number(-5)]).unwrap(), Value::Number(5)); // Unary minus of negative
        assert_eq!(
            builtin_sub(&[Value::Number(10), Value::Number(3), Value::Number(2)]).unwrap(),
            Value::Number(5)
        ); // Multiple subtraction
        assert_eq!(
            builtin_sub(&[Value::Number(0), Value::Number(5)]).unwrap(),
            Value::Number(-5)
        ); // Zero minus number
        assert_eq!(
            builtin_sub(&[Value::Number(10), Value::Number(0)]).unwrap(),
            Value::Number(10)
        ); // Number minus zero

        // Test subtraction error cases
        assert!(builtin_sub(&[]).is_err()); // No arguments
        assert!(builtin_sub(&[Value::String("not a number".to_string())]).is_err());
        assert!(builtin_sub(&[Value::Number(5), Value::Bool(false)]).is_err());

        // Test arithmetic functions - multiplication
        // SCHEME-STRICT: We require at least 1 argument (Scheme R7RS allows 0 args, returns 1)
        assert!(builtin_mul(&[]).is_err()); // No arguments should error
        assert_eq!(builtin_mul(&[Value::Number(5)]).unwrap(), Value::Number(5)); // Single number
        assert_eq!(
            builtin_mul(&[Value::Number(2), Value::Number(3), Value::Number(4)]).unwrap(),
            Value::Number(24)
        ); // Multiple numbers
        assert_eq!(
            builtin_mul(&[Value::Number(-2), Value::Number(3)]).unwrap(),
            Value::Number(-6)
        ); // Negative numbers
        assert_eq!(
            builtin_mul(&[Value::Number(0), Value::Number(100)]).unwrap(),
            Value::Number(0)
        ); // Zero multiplication
        assert_eq!(
            builtin_mul(&[Value::Number(1), Value::Number(1), Value::Number(1)]).unwrap(),
            Value::Number(1)
        ); // Ones

        // Test multiplication error cases
        assert!(builtin_mul(&[Value::String("not a number".to_string())]).is_err());
        assert!(builtin_mul(&[Value::Number(2), Value::List(vec![])]).is_err());

        // Test all comparison functions comprehensively
        // Greater than
        assert_eq!(
            builtin_gt(&[Value::Number(5), Value::Number(3)]).unwrap(),
            Value::Bool(true)
        );
        assert_eq!(
            builtin_gt(&[Value::Number(3), Value::Number(5)]).unwrap(),
            Value::Bool(false)
        );
        assert_eq!(
            builtin_gt(&[Value::Number(5), Value::Number(5)]).unwrap(),
            Value::Bool(false)
        ); // Equal case
        assert_eq!(
            builtin_gt(&[Value::Number(-1), Value::Number(-2)]).unwrap(),
            Value::Bool(true)
        ); // Negative numbers

        // Greater than or equal
        assert_eq!(
            builtin_ge(&[Value::Number(5), Value::Number(3)]).unwrap(),
            Value::Bool(true)
        );
        assert_eq!(
            builtin_ge(&[Value::Number(3), Value::Number(5)]).unwrap(),
            Value::Bool(false)
        );
        assert_eq!(
            builtin_ge(&[Value::Number(5), Value::Number(5)]).unwrap(),
            Value::Bool(true)
        ); // Equal case

        // Less than
        assert_eq!(
            builtin_lt(&[Value::Number(3), Value::Number(5)]).unwrap(),
            Value::Bool(true)
        );
        assert_eq!(
            builtin_lt(&[Value::Number(5), Value::Number(3)]).unwrap(),
            Value::Bool(false)
        );
        assert_eq!(
            builtin_lt(&[Value::Number(5), Value::Number(5)]).unwrap(),
            Value::Bool(false)
        ); // Equal case

        // Less than or equal
        assert_eq!(
            builtin_le(&[Value::Number(3), Value::Number(5)]).unwrap(),
            Value::Bool(true)
        );
        assert_eq!(
            builtin_le(&[Value::Number(5), Value::Number(3)]).unwrap(),
            Value::Bool(false)
        );
        assert_eq!(
            builtin_le(&[Value::Number(5), Value::Number(5)]).unwrap(),
            Value::Bool(true)
        ); // Equal case

        // Numeric equality
        assert_eq!(
            builtin_eq(&[Value::Number(5), Value::Number(5)]).unwrap(),
            Value::Bool(true)
        );
        assert_eq!(
            builtin_eq(&[Value::Number(5), Value::Number(3)]).unwrap(),
            Value::Bool(false)
        );
        assert_eq!(
            builtin_eq(&[Value::Number(0), Value::Number(0)]).unwrap(),
            Value::Bool(true)
        );
        assert_eq!(
            builtin_eq(&[Value::Number(-1), Value::Number(-1)]).unwrap(),
            Value::Bool(true)
        );

        // Test comparison error cases (wrong number of args or wrong types)
        assert!(builtin_gt(&[Value::Number(5)]).is_err()); // Too few args
        // Test chaining behavior: 5 > 3 > 1 should be false since 3 > 1 is true, so chain is true
        assert_eq!(
            builtin_gt(&[Value::Number(5), Value::Number(3), Value::Number(1)]).unwrap(),
            Value::Bool(true)
        );
        // Test chaining that should fail: 5 > 3 > 4 should be false since 3 > 4 is false
        assert_eq!(
            builtin_gt(&[Value::Number(5), Value::Number(3), Value::Number(4)]).unwrap(),
            Value::Bool(false)
        );
        assert!(builtin_gt(&[Value::String("a".to_string()), Value::Number(3)]).is_err()); // Wrong type

        // Test structural equality (equal?)
        assert_eq!(
            builtin_equal(&[Value::Number(5), Value::Number(5)]).unwrap(),
            Value::Bool(true)
        );
        assert_eq!(
            builtin_equal(&[Value::Number(5), Value::Number(3)]).unwrap(),
            Value::Bool(false)
        );
        assert_eq!(
            builtin_equal(&[
                Value::String("hello".to_string()),
                Value::String("hello".to_string())
            ])
            .unwrap(),
            Value::Bool(true)
        );
        assert_eq!(
            builtin_equal(&[
                Value::String("hello".to_string()),
                Value::String("world".to_string())
            ])
            .unwrap(),
            Value::Bool(false)
        );
        assert_eq!(
            builtin_equal(&[Value::Bool(true), Value::Bool(true)]).unwrap(),
            Value::Bool(true)
        );
        assert_eq!(
            builtin_equal(&[Value::Bool(true), Value::Bool(false)]).unwrap(),
            Value::Bool(false)
        );
        assert_eq!(
            builtin_equal(&[Value::List(vec![]), Value::List(vec![])]).unwrap(),
            Value::Bool(true)
        );
        assert_eq!(
            builtin_equal(&[
                Value::List(vec![Value::Number(1)]),
                Value::List(vec![Value::Number(1)])
            ])
            .unwrap(),
            Value::Bool(true)
        );
        assert_eq!(
            builtin_equal(&[Value::Number(5), Value::String("5".to_string())]).unwrap(),
            Value::Bool(false)
        ); // Different types

        // Test equal? error cases
        assert!(builtin_equal(&[Value::Number(5)]).is_err()); // Too few args
        assert!(builtin_equal(&[Value::Number(5), Value::Number(3), Value::Number(1)]).is_err()); // Too many args

        // Test numeric comparison chaining
        assert_eq!(
            builtin_lt(&[Value::Number(1), Value::Number(2), Value::Number(3)]).unwrap(),
            Value::Bool(true)
        ); // 1 < 2 < 3
        assert_eq!(
            builtin_lt(&[Value::Number(1), Value::Number(3), Value::Number(2)]).unwrap(),
            Value::Bool(false)
        ); // 1 < 3 but not 3 < 2
        assert_eq!(
            builtin_eq(&[Value::Number(5), Value::Number(5), Value::Number(5)]).unwrap(),
            Value::Bool(true)
        ); // 5 = 5 = 5
        assert_eq!(
            builtin_eq(&[Value::Number(5), Value::Number(5), Value::Number(3)]).unwrap(),
            Value::Bool(false)
        ); // 5 = 5 but not 5 = 3

        // Test logical functions - not
        assert_eq!(
            builtin_not(&[Value::Bool(true)]).unwrap(),
            Value::Bool(false)
        );
        assert_eq!(
            builtin_not(&[Value::Bool(false)]).unwrap(),
            Value::Bool(true)
        );

        // Test not error cases
        assert!(builtin_not(&[]).is_err()); // No args
        assert!(builtin_not(&[Value::Bool(true), Value::Bool(false)]).is_err()); // Too many args
        assert!(builtin_not(&[Value::Number(1)]).is_err()); // Wrong type
        assert!(builtin_not(&[Value::String("true".to_string())]).is_err()); // Wrong type

        // Test list functions - car
        let list = Value::List(vec![Value::Number(1), Value::Number(2), Value::Number(3)]);
        assert_eq!(builtin_car(&[list.clone()]).unwrap(), Value::Number(1));
        let single_elem_list = Value::List(vec![Value::String("only".to_string())]);
        assert_eq!(
            builtin_car(&[single_elem_list]).unwrap(),
            Value::String("only".to_string())
        );
        let nested_list = Value::List(vec![Value::List(vec![Value::Number(1)]), Value::Number(2)]);
        assert_eq!(
            builtin_car(&[nested_list]).unwrap(),
            Value::List(vec![Value::Number(1)])
        );

        // Test car error cases
        assert!(builtin_car(&[]).is_err()); // No args
        assert!(builtin_car(&[list.clone(), list.clone()]).is_err()); // Too many args
        assert!(builtin_car(&[Value::List(vec![])]).is_err()); // Empty list
        assert!(builtin_car(&[Value::Number(42)]).is_err()); // Not a list
        assert!(builtin_car(&[Value::String("not a list".to_string())]).is_err()); // Not a list

        // Test list functions - cdr
        let list = Value::List(vec![Value::Number(1), Value::Number(2), Value::Number(3)]);
        assert_eq!(
            builtin_cdr(&[list.clone()]).unwrap(),
            Value::List(vec![Value::Number(2), Value::Number(3)])
        );
        let single_elem_list = Value::List(vec![Value::String("only".to_string())]);
        assert_eq!(
            builtin_cdr(&[single_elem_list]).unwrap(),
            Value::List(vec![])
        );
        let two_elem_list = Value::List(vec![Value::Number(1), Value::Number(2)]);
        assert_eq!(
            builtin_cdr(&[two_elem_list]).unwrap(),
            Value::List(vec![Value::Number(2)])
        );

        // Test cdr error cases
        assert!(builtin_cdr(&[]).is_err()); // No args
        assert!(builtin_cdr(&[list.clone(), list.clone()]).is_err()); // Too many args
        assert!(builtin_cdr(&[Value::List(vec![])]).is_err()); // Empty list
        assert!(builtin_cdr(&[Value::Bool(true)]).is_err()); // Not a list

        // Test list functions - cons
        let new_list = builtin_cons(&[
            Value::Number(0),
            Value::List(vec![Value::Number(1), Value::Number(2)]),
        ])
        .unwrap();
        assert_eq!(
            new_list,
            Value::List(vec![Value::Number(0), Value::Number(1), Value::Number(2)])
        );
        let cons_to_empty =
            builtin_cons(&[Value::String("first".to_string()), Value::List(vec![])]).unwrap();
        assert_eq!(
            cons_to_empty,
            Value::List(vec![Value::String("first".to_string())])
        );
        let cons_nested = builtin_cons(&[
            Value::List(vec![Value::Number(1)]),
            Value::List(vec![Value::Number(2)]),
        ])
        .unwrap();
        assert_eq!(
            cons_nested,
            Value::List(vec![Value::List(vec![Value::Number(1)]), Value::Number(2)])
        );

        // Test cons error cases
        assert!(builtin_cons(&[]).is_err()); // No args
        assert!(builtin_cons(&[Value::Number(1)]).is_err()); // Too few args
        assert!(builtin_cons(&[Value::Number(1), Value::Number(2), Value::Number(3)]).is_err()); // Too many args
        assert!(builtin_cons(&[Value::Number(1), Value::Number(2)]).is_err()); // Second arg not a list
        assert!(
            builtin_cons(&[Value::Number(1), Value::String("not a list".to_string())]).is_err()
        ); // Second arg not a list

        // Test list functions - list
        assert_eq!(builtin_list(&[]).unwrap(), Value::List(vec![])); // Empty list
        assert_eq!(
            builtin_list(&[Value::Number(1)]).unwrap(),
            Value::List(vec![Value::Number(1)])
        ); // Single element
        assert_eq!(
            builtin_list(&[
                Value::Number(1),
                Value::String("hello".to_string()),
                Value::Bool(true)
            ])
            .unwrap(),
            Value::List(vec![
                Value::Number(1),
                Value::String("hello".to_string()),
                Value::Bool(true)
            ])
        ); // Mixed types
        let nested =
            builtin_list(&[Value::List(vec![Value::Number(1)]), Value::Number(2)]).unwrap();
        assert_eq!(
            nested,
            Value::List(vec![Value::List(vec![Value::Number(1)]), Value::Number(2)])
        ); // Nested lists

        // Test null? function
        assert_eq!(
            builtin_null(&[Value::List(vec![])]).unwrap(),
            Value::Bool(true)
        ); // Empty list is nil
        assert_eq!(
            builtin_null(&[Value::Number(42)]).unwrap(),
            Value::Bool(false)
        ); // Number is not nil
        assert_eq!(
            builtin_null(&[Value::String("".to_string())]).unwrap(),
            Value::Bool(false)
        ); // Empty string is not nil
        assert_eq!(
            builtin_null(&[Value::Bool(false)]).unwrap(),
            Value::Bool(false)
        ); // False is not nil
        assert_eq!(
            builtin_null(&[Value::List(vec![Value::Number(1)])]).unwrap(),
            Value::Bool(false)
        ); // Non-empty list is not nil

        // Test null? error cases
        assert!(builtin_null(&[]).is_err()); // No args
        assert!(builtin_null(&[Value::Number(1), Value::Number(2)]).is_err()); // Too many args

        // Test error function
        assert!(builtin_error(&[]).is_err()); // No args - should produce generic error
        assert!(builtin_error(&[Value::String("test error".to_string())]).is_err()); // String message
        assert!(builtin_error(&[Value::Number(42)]).is_err()); // Number message  
        assert!(builtin_error(&[Value::Bool(true)]).is_err()); // Bool message
        assert!(
            builtin_error(&[
                Value::String("Error:".to_string()),
                Value::String("Something went wrong".to_string())
            ])
            .is_err()
        ); // Multiple args

        // Verify error messages are constructed correctly
        match builtin_error(&[Value::String("test message".to_string())]) {
            Err(SchemeError::EvalError(msg)) => assert_eq!(msg, "test message"),
            _ => panic!("Expected EvalError with specific message"),
        }

        match builtin_error(&[Value::String("Error:".to_string()), Value::Number(404)]) {
            Err(SchemeError::EvalError(msg)) => assert_eq!(msg, "Error: 404"),
            _ => panic!("Expected EvalError with concatenated message"),
        }
    }

    #[test]
    fn test_mapping_functions() {
        // Test JSONLogic to Scheme mapping using direct lookup
        assert_eq!(
            find_builtin_op_by_jsonlogic_id("!").unwrap().scheme_id,
            "not"
        );
        assert_eq!(
            find_builtin_op_by_jsonlogic_id("==").unwrap().scheme_id,
            "equal?"
        );
        assert_eq!(find_builtin_op_by_jsonlogic_id("+").unwrap().scheme_id, "+");

        // Test Scheme to JSONLogic mapping using the registry
        assert_eq!(map_scheme_id_to_jsonlogic_id("not"), "!");
        assert_eq!(map_scheme_id_to_jsonlogic_id("equal?"), "==");
        assert_eq!(map_scheme_id_to_jsonlogic_id("+"), "+"); // Same in both
        assert_eq!(map_scheme_id_to_jsonlogic_id("unknown"), "unknown"); // Fallback

        // Test expanded mappings - arithmetic operations
        assert_eq!(find_builtin_op_by_jsonlogic_id("-").unwrap().scheme_id, "-");
        assert_eq!(find_builtin_op_by_jsonlogic_id("*").unwrap().scheme_id, "*");
        assert_eq!(find_builtin_op_by_jsonlogic_id(">").unwrap().scheme_id, ">");

        // Test shared control flow operations (no prefix)
        assert_eq!(
            find_builtin_op_by_jsonlogic_id("and").unwrap().scheme_id,
            "and"
        );
        assert_eq!(
            find_builtin_op_by_jsonlogic_id("or").unwrap().scheme_id,
            "or"
        );
        assert_eq!(
            find_builtin_op_by_jsonlogic_id("if").unwrap().scheme_id,
            "if"
        );

        // Test Scheme-specific operations with prefixes
        assert_eq!(
            find_builtin_op_by_jsonlogic_id("scheme-car")
                .unwrap()
                .scheme_id,
            "car"
        );
        assert_eq!(
            find_builtin_op_by_jsonlogic_id("scheme-numeric-equals")
                .unwrap()
                .scheme_id,
            "="
        );
    }

    #[test]
    fn test_lookup_functions() {
        // Test builtin detection by scheme id
        assert!(find_builtin_op_by_scheme_id("+").is_some());
        assert!(find_builtin_op_by_scheme_id("not").is_some());
        assert!(find_builtin_op_by_scheme_id("equal?").is_some());
        assert!(find_builtin_op_by_scheme_id("unknown").is_none());

        // Test builtin detection by jsonlogic id
        assert!(find_builtin_op_by_jsonlogic_id("!").is_some());
        assert!(find_builtin_op_by_jsonlogic_id("==").is_some());
        assert!(find_builtin_op_by_jsonlogic_id("unknown").is_none());

        // Test special form detection using available functions
        assert!(
            find_builtin_op_by_scheme_id("and")
                .map(|op| op.is_special_form())
                .unwrap_or(false)
        );
        assert!(
            find_builtin_op_by_scheme_id("or")
                .map(|op| op.is_special_form())
                .unwrap_or(false)
        );
        assert!(
            find_builtin_op_by_scheme_id("if")
                .map(|op| op.is_special_form())
                .unwrap_or(false)
        );
        assert!(
            find_builtin_op_by_scheme_id("not")
                .map(|op| !op.is_special_form())
                .unwrap_or(true)
        );
        assert!(
            find_builtin_op_by_scheme_id("+")
                .map(|op| !op.is_special_form())
                .unwrap_or(true)
        );

        // Test that get_builtin_ops returns all operations
        let all_ops = get_builtin_ops();
        assert!(!all_ops.is_empty());

        // Verify we can find specific operations
        let add_op = all_ops.iter().find(|op| op.scheme_id == "+");
        assert!(add_op.is_some());
        assert!(!add_op.unwrap().is_special_form());

        let and_op = all_ops.iter().find(|op| op.scheme_id == "and");
        assert!(and_op.is_some());
        assert!(and_op.unwrap().is_special_form());
    }

    #[test]
    fn test_arity_validation() {
        // Test Arity::Exact validation
        assert!(Arity::Exact(2).validate(2).is_ok());
        assert!(Arity::Exact(2).validate(1).is_err());
        assert!(Arity::Exact(2).validate(3).is_err());

        // Test Arity::AtLeast validation
        assert!(Arity::AtLeast(1).validate(1).is_ok());
        assert!(Arity::AtLeast(1).validate(2).is_ok());
        assert!(Arity::AtLeast(1).validate(0).is_err());

        // Test Arity::Range validation
        assert!(Arity::Range(1, 3).validate(1).is_ok());
        assert!(Arity::Range(1, 3).validate(2).is_ok());
        assert!(Arity::Range(1, 3).validate(3).is_ok());
        assert!(Arity::Range(1, 3).validate(0).is_err());
        assert!(Arity::Range(1, 3).validate(4).is_err());

        // Test Arity::Any validation
        assert!(Arity::Any.validate(0).is_ok());
        assert!(Arity::Any.validate(1).is_ok());
        assert!(Arity::Any.validate(100).is_ok());

        // Test error messages
        match Arity::Exact(2).validate(1) {
            Err(SchemeError::ArityError { expected, got, .. }) => {
                assert_eq!(expected, 2);
                assert_eq!(got, 1);
            }
            _ => panic!("Expected ArityError"),
        }
    }
}
