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
use crate::ast::{Value, nil, sym, val};
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

/// Find a builtin operation by its Scheme identifier
pub fn find_scheme_op(id: &str) -> Option<&'static BuiltinOp> {
    BUILTIN_SCHEME.get(id).copied()
}

/// Find a builtin operation by its JSONLogic identifier  
pub fn find_jsonlogic_op(id: &str) -> Option<&'static BuiltinOp> {
    BUILTIN_JSONLOGIC.get(id).copied()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_builtin_ops_registry() {
        // Test lookup by both scheme and jsonlogic ids
        let not_op = find_scheme_op("not").unwrap();
        assert_eq!(not_op.jsonlogic_id, "!");
        assert_eq!(not_op.arity, Arity::Exact(1));
        assert!(!not_op.is_special_form());

        let not_by_jsonlogic = find_jsonlogic_op("!").unwrap();
        assert!(std::ptr::eq(not_op, not_by_jsonlogic)); // Same operation

        // Test function execution
        let add_op = find_scheme_op("+").unwrap();
        assert_eq!(add_op.arity, Arity::AtLeast(0));
        assert!(!add_op.is_special_form());

        if let OpKind::Function(func) = &add_op.op_kind {
            let result = func(&[val(1), val(2)]).unwrap();
            assert_eq!(result, val(3));
        } else {
            panic!("Expected Function variant");
        }

        // Test special forms
        let if_op = find_scheme_op("if").unwrap();
        assert!(if_op.is_special_form());
        assert_eq!(if_op.arity, Arity::Exact(3));

        // Test that get_builtin_ops returns all operations
        let all_ops = get_builtin_ops();
        assert!(!all_ops.is_empty());

        // Verify we can find specific operations
        let add_op = all_ops.iter().find(|op| op.scheme_id == "+");
        assert!(add_op.is_some());
        assert!(!add_op.unwrap().is_special_form());

        let quote_op = all_ops.iter().find(|op| op.scheme_id == "quote");
        assert!(quote_op.is_some());
        assert!(quote_op.unwrap().is_special_form());

        // Test unknown operations return None
        assert!(find_scheme_op("unknown").is_none());
        assert!(find_jsonlogic_op("unknown").is_none());

        // Test operator mappings
        // JSONLogic to Scheme mapping
        assert_eq!(find_jsonlogic_op("!").unwrap().scheme_id, "not");
        assert_eq!(find_jsonlogic_op("==").unwrap().scheme_id, "equal?");
        assert_eq!(find_jsonlogic_op("+").unwrap().scheme_id, "+");

        // Scheme to JSONLogic mapping (test inline conversion)
        assert_eq!(find_scheme_op("not").unwrap().jsonlogic_id, "!");
        assert_eq!(find_scheme_op("equal?").unwrap().jsonlogic_id, "==");
        assert_eq!(find_scheme_op("+").unwrap().jsonlogic_id, "+"); // Same in both

        // Test arithmetic operations
        assert_eq!(find_jsonlogic_op("-").unwrap().scheme_id, "-");
        assert_eq!(find_jsonlogic_op("*").unwrap().scheme_id, "*");
        assert_eq!(find_jsonlogic_op(">").unwrap().scheme_id, ">");

        // Test control flow operations (no prefix)
        assert_eq!(find_jsonlogic_op("and").unwrap().scheme_id, "and");
        assert_eq!(find_jsonlogic_op("or").unwrap().scheme_id, "or");
        assert_eq!(find_jsonlogic_op("if").unwrap().scheme_id, "if");

        // Test Scheme-specific operations with prefixes
        assert_eq!(find_jsonlogic_op("scheme-car").unwrap().scheme_id, "car");
        assert_eq!(
            find_jsonlogic_op("scheme-numeric-equals")
                .unwrap()
                .scheme_id,
            "="
        );
    }

    #[test]
    fn test_builtin_function_implementations() {
        // Pre-declare list for tests that need variable reuse
        let int_list = val([1, 2, 3]);

        let test_cases = [
            // Test arithmetic functions - addition
            (builtin_add(&[]), Some(val(0))),       // Identity
            (builtin_add(&[val(5)]), Some(val(5))), // Single number
            (builtin_add(&[val(1), val(2), val(3)]), Some(val(6))), // Multiple numbers
            (builtin_add(&[val(-5), val(10)]), Some(val(5))), // Negative numbers
            (builtin_add(&[val(0), val(0), val(0)]), Some(val(0))), // Zeros
            // Test addition error cases
            (builtin_add(&[val("not a number")]), None), // Invalid type
            (builtin_add(&[val(1), val(true)]), None),   // Mixed types
            // Test arithmetic functions - subtraction
            (builtin_sub(&[val(5)]), Some(val(-5))), // Unary minus
            (builtin_sub(&[val(-5)]), Some(val(5))), // Unary minus of negative
            (builtin_sub(&[val(10), val(3), val(2)]), Some(val(5))), // Multiple subtraction
            (builtin_sub(&[val(0), val(5)]), Some(val(-5))), // Zero minus number
            (builtin_sub(&[val(10), val(0)]), Some(val(10))), // Number minus zero
            // Test subtraction error cases
            (builtin_sub(&[]), None), // No arguments
            (builtin_sub(&[val("not a number")]), None),
            (builtin_sub(&[val(5), val(false)]), None),
            // Test arithmetic functions - multiplication
            // SCHEME-STRICT: We require at least 1 argument (Scheme R7RS allows 0 args, returns 1)
            (builtin_mul(&[]), None), // No arguments should error
            (builtin_mul(&[val(5)]), Some(val(5))), // Single number
            (builtin_mul(&[val(2), val(3), val(4)]), Some(val(24))), // Multiple numbers
            (builtin_mul(&[val(-2), val(3)]), Some(val(-6))), // Negative numbers
            (builtin_mul(&[val(0), val(100)]), Some(val(0))), // Zero multiplication
            (builtin_mul(&[val(1), val(1), val(1)]), Some(val(1))), // Ones
            // Test multiplication error cases
            (builtin_mul(&[val("not a number")]), None),
            (builtin_mul(&[val(2), nil()]), None),
            // Test comparison functions - greater than
            (builtin_gt(&[val(5), val(3)]), Some(val(true))),
            (builtin_gt(&[val(3), val(5)]), Some(val(false))),
            (builtin_gt(&[val(5), val(5)]), Some(val(false))), // Equal case
            (builtin_gt(&[val(-1), val(-2)]), Some(val(true))), // Negative numbers
            // Test chaining behavior: 5 > 3 > 1 should be true since all adjacent pairs satisfy >
            (builtin_gt(&[val(5), val(3), val(1)]), Some(val(true))), // Chaining true
            // Test chaining that should fail: 5 > 3 > 4 should be false since 3 > 4 is false
            (builtin_gt(&[val(5), val(3), val(4)]), Some(val(false))), // Chaining false
            // Test comparison error cases (wrong number of args or wrong types)
            (builtin_gt(&[val(5)]), None),           // Too few args
            (builtin_gt(&[val("a"), val(3)]), None), // Wrong type
            // Test comparison functions - greater than or equal
            (builtin_ge(&[val(5), val(3)]), Some(val(true))),
            (builtin_ge(&[val(3), val(5)]), Some(val(false))),
            (builtin_ge(&[val(5), val(5)]), Some(val(true))), // Equal case
            // Test comparison functions - less than
            (builtin_lt(&[val(3), val(5)]), Some(val(true))),
            (builtin_lt(&[val(5), val(3)]), Some(val(false))),
            (builtin_lt(&[val(5), val(5)]), Some(val(false))), // Equal case
            // Test numeric comparison chaining: 1 < 2 < 3 (all adjacent pairs satisfy <)
            (builtin_lt(&[val(1), val(2), val(3)]), Some(val(true))), // Chaining true
            // Test chaining that should fail: 1 < 3 but not 3 < 2
            (builtin_lt(&[val(1), val(3), val(2)]), Some(val(false))), // Chaining false
            // Test comparison functions - less than or equal
            (builtin_le(&[val(3), val(5)]), Some(val(true))),
            (builtin_le(&[val(5), val(3)]), Some(val(false))),
            (builtin_le(&[val(5), val(5)]), Some(val(true))), // Equal case
            // Test numeric equality
            (builtin_eq(&[val(5), val(5)]), Some(val(true))),
            (builtin_eq(&[val(5), val(3)]), Some(val(false))),
            (builtin_eq(&[val(0), val(0)]), Some(val(true))),
            (builtin_eq(&[val(-1), val(-1)]), Some(val(true))),
            (builtin_eq(&[val(5), val(5), val(5)]), Some(val(true))), // 5 = 5 = 5 (all equal)
            (builtin_eq(&[val(5), val(5), val(3)]), Some(val(false))), // 5 = 5 but not 5 = 3
            // Test structural equality (equal?)
            (builtin_equal(&[val(5), val(5)]), Some(val(true))),
            (builtin_equal(&[val(5), val(3)]), Some(val(false))),
            (
                builtin_equal(&[val("hello"), val("hello")]),
                Some(val(true)),
            ),
            (
                builtin_equal(&[val("hello"), val("world")]),
                Some(val(false)),
            ),
            (builtin_equal(&[val(true), val(true)]), Some(val(true))),
            (builtin_equal(&[val(true), val(false)]), Some(val(false))),
            (builtin_equal(&[nil(), nil()]), Some(val(true))),
            (builtin_equal(&[val([1]), val([1])]), Some(val(true))),
            (builtin_equal(&[val(5), val("5")]), Some(val(false))), // Different types
            // Test equal? error cases (structural equality requires exactly 2 args)
            (builtin_equal(&[val(5)]), None), // Too few args
            (builtin_equal(&[val(5), val(3), val(1)]), None), // Too many args
            // Test logical functions - not
            (builtin_not(&[val(true)]), Some(val(false))),
            (builtin_not(&[val(false)]), Some(val(true))),
            // Test not error cases
            (builtin_not(&[]), None),                      // No args
            (builtin_not(&[val(true), val(false)]), None), // Too many args
            (builtin_not(&[val(1)]), None),                // Wrong type
            (builtin_not(&[val("true")]), None),           // Wrong type
            // Test list functions - car
            (builtin_car(&[val([1, 2, 3])]), Some(val(1))), // First element
            (builtin_car(&[val(["only"])]), Some(val("only"))), // Single element
            (builtin_car(&[val([val([1]), val(2)])]), Some(val([1]))), // Nested list
            // Test car error cases
            (builtin_car(&[]), None), // No args
            (builtin_car(&[int_list.clone(), int_list.clone()]), None), // Too many args
            (builtin_car(&[nil()]), None), // Empty list
            (builtin_car(&[val(42)]), None), // Not a list
            (builtin_car(&[val("not a list")]), None), // Not a list
            // Test list functions - cdr
            (builtin_cdr(&[val([1, 2, 3])]), Some(val([2, 3]))), // Rest of list
            (builtin_cdr(&[val(["only"])]), Some(nil())),        // Single element -> empty
            (builtin_cdr(&[val([1, 2])]), Some(val([2]))),       // Two elements
            // Test cdr error cases
            (builtin_cdr(&[]), None), // No args
            (builtin_cdr(&[int_list.clone(), int_list.clone()]), None), // Too many args
            (builtin_cdr(&[nil()]), None), // Empty list
            (builtin_cdr(&[val(true)]), None), // Not a list
            // Test list functions - cons
            (builtin_cons(&[val(0), val([1, 2])]), Some(val([0, 1, 2]))), // Prepend to list
            (builtin_cons(&[val("first"), nil()]), Some(val(["first"]))), // Cons to empty
            (
                builtin_cons(&[val([1]), val([2])]),
                Some(val([val([1]), val(2)])),
            ), // Nested cons
            // Test cons error cases
            (builtin_cons(&[]), None),                          // No args
            (builtin_cons(&[val(1)]), None),                    // Too few args
            (builtin_cons(&[val(1), val(2), val(3)]), None),    // Too many args
            (builtin_cons(&[val(1), val(2)]), None),            // Second arg not a list
            (builtin_cons(&[val(1), val("not a list")]), None), // Second arg not a list
            // Test list functions - list
            (builtin_list(&[]), Some(nil())),          // Empty list
            (builtin_list(&[val(1)]), Some(val([1]))), // Single element
            (
                builtin_list(&[val(1), val("hello"), val(true)]),
                Some(val([val(1), val("hello"), val(true)])),
            ), // Mixed types
            (
                builtin_list(&[val([1]), val(2)]),
                Some(val([val([1]), val(2)])),
            ), // Nested lists
            // Test null? function
            (builtin_null(&[nil()]), Some(val(true))), // Empty list is nil
            (builtin_null(&[val(42)]), Some(val(false))), // Number is not nil
            (builtin_null(&[val("")]), Some(val(false))), // Empty string is not nil
            (builtin_null(&[val(false)]), Some(val(false))), // False is not nil
            (builtin_null(&[val([1])]), Some(val(false))), // Non-empty list is not nil
            // Test null? error cases
            (builtin_null(&[]), None),               // No args
            (builtin_null(&[val(1), val(2)]), None), // Too many args
            // Test error function
            (builtin_error(&[]), None), // No args - should produce generic error
            (builtin_error(&[val("test error")]), None), // String message
            (builtin_error(&[val(42)]), None), // Number message
            (builtin_error(&[val(true)]), None), // Bool message
            (
                builtin_error(&[val("Error:"), val("Something went wrong")]),
                None,
            ), // Multiple args
        ];

        for (expression, expected_result) in test_cases {
            match expression {
                Ok(result) => assert_eq!(Some(result), expected_result),
                Err(_) => assert_eq!(expected_result, None),
            }
        }

        // Verify error messages are constructed correctly (can't be in array because needs specific match)
        match builtin_error(&[val("test message")]).unwrap_err() {
            SchemeError::EvalError(msg) => assert_eq!(msg, "test message"),
            _ => panic!("Expected EvalError with specific message"),
        }

        match builtin_error(&[val("Error:"), val(404)]).unwrap_err() {
            SchemeError::EvalError(msg) => assert_eq!(msg, "Error: 404"),
            _ => panic!("Expected EvalError with concatenated message"),
        }
    }

    #[test]
    fn test_arity_validation() {
        use Arity::*;

        // Test Exact validation
        Exact(2).validate(2).unwrap();
        Exact(2).validate(1).unwrap_err();
        Exact(2).validate(3).unwrap_err();

        // Test AtLeast validation
        AtLeast(1).validate(1).unwrap();
        AtLeast(1).validate(2).unwrap();
        AtLeast(1).validate(0).unwrap_err();

        // Test Range validation
        Range(1, 3).validate(1).unwrap();
        Range(1, 3).validate(2).unwrap();
        Range(1, 3).validate(3).unwrap();
        Range(1, 3).validate(0).unwrap_err();
        Range(1, 3).validate(4).unwrap_err();

        // Test Any validation
        Any.validate(0).unwrap();
        Any.validate(1).unwrap();
        Any.validate(100).unwrap();

        // Test error messages
        match Exact(2).validate(1).unwrap_err() {
            SchemeError::ArityError { expected, got, .. } => {
                assert_eq!(expected, 2);
                assert_eq!(got, 1);
            }
            _ => panic!("Expected ArityError"),
        }
    }
}
