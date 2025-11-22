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
//! 1. **Implement the function** following the signature `fn(args: &[Value]) -> Result<Value, Error>`
//! 2. **Add to BUILTIN_OPS** with Scheme identifier and arity
//! 3. **Add to BUILTIN_OPS_JSONLOGIC** if it has a different JSONLogic identifier
//! 4. **Update evaluator** if it's a special form requiring custom evaluation logic
//! 5. **Add comprehensive tests** covering edge cases and error conditions

use crate::Error;
use crate::ast::{NumberType, Value};
use crate::evaluator::intooperation::{IntoOperation, IntoVariadicOperation, OperationFn};
use crate::evaluator::{
    Arity, Environment, NumIter, StringIter, ValueIter, eval_and, eval_define, eval_if,
    eval_lambda, eval_or, eval_quote,
};
use std::collections::HashMap;
use std::sync::{Arc, LazyLock};

/// Represents the implementation of a built-in expression (function or special form)
#[derive(Clone)]
pub enum OpKind {
    /// Regular function that takes evaluated arguments and returns a value
    /// via the canonical erased builtin signature used by the evaluator.
    Function(Arc<OperationFn>),
    /// Special form that requires access to the environment, unevaluated arguments and current evaluation stack depth
    SpecialForm(fn(&[Value], &mut Environment, usize) -> Result<Value, Error>),
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
            (OpKind::Function(f1), OpKind::Function(f2)) => Arc::ptr_eq(f1, f2),
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
    #[cfg_attr(not(test), expect(dead_code))]
    pub(crate) fn is_special_form(&self) -> bool {
        matches!(self.op_kind, OpKind::SpecialForm(_))
    }

    /// Check if the given number of arguments is valid for this operation
    pub(crate) fn validate_arity(&self, arg_count: usize) -> Result<(), Error> {
        self.arity.validate(arg_count)
    }
}

//
// Builtin Function Implementations
//

// Macro to generate numeric comparison functions
macro_rules! numeric_comparison {
    ($name:ident, $op:tt, $op_str:expr) => {
        fn $name(first: NumberType, rest: NumIter<'_>) -> Result<bool, Error> {
            let mut iter = rest.peekable();

            // SCHEME-JSONLOGIC-STRICT: Require at least 2 arguments (both
            // standards allow < 2 args but with different semantics).
            // If there is no second operand, we have only one argument.
            if iter.peek().is_none() {
                return Err(Error::arity_error(2, 1));
            }

            // Chain comparisons: all adjacent pairs must satisfy the comparison.
            // Start with the first argument, then compare each subsequent
            // element against the previous one.
            let mut prev = first;
            for current in iter {
                if !(prev $op current) {
                    return Ok(false);
                }
                prev = current;
            }

            Ok(true)
        }
    };
}

// Generate all comparison functions
numeric_comparison!(builtin_eq, ==, "=");
numeric_comparison!(builtin_lt, <, "<");
numeric_comparison!(builtin_gt, >, ">");
numeric_comparison!(builtin_le, <=, "<=");
numeric_comparison!(builtin_ge, >=, ">=");

fn builtin_add(args: NumIter<'_>) -> Result<NumberType, Error> {
    let mut sum = 0 as NumberType;
    for arg in args {
        sum = sum
            .checked_add(arg)
            .ok_or_else(|| Error::EvalError("Integer overflow in addition".into()))?;
    }
    Ok(sum)
}

fn builtin_sub(first: NumberType, rest: NumIter<'_>) -> Result<NumberType, Error> {
    let mut iter = rest.peekable();

    if iter.peek().is_none() {
        return first
            .checked_neg()
            .ok_or_else(|| Error::EvalError("Integer overflow in negation".into()));
    }

    let mut result = first;
    for n in iter {
        result = result
            .checked_sub(n)
            .ok_or_else(|| Error::EvalError("Integer overflow in subtraction".into()))?;
    }

    Ok(result)
}

// SCHEME-STRICT: Require at least 1 argument (Scheme R7RS allows 0 args, returns 1)
fn builtin_mul(first: NumberType, rest: NumIter<'_>) -> Result<NumberType, Error> {
    let mut product = first;
    for n in rest {
        product = product
            .checked_mul(n)
            .ok_or_else(|| Error::EvalError("Integer overflow in multiplication".into()))?;
    }
    Ok(product)
}

fn builtin_car(mut list: ValueIter<'_>) -> Result<Value, Error> {
    match list.next() {
        Some(first) => Ok(first.clone()),
        None => Err(Error::EvalError("car of empty list".into())),
    }
}

fn builtin_cdr(mut list: ValueIter<'_>) -> Result<Value, Error> {
    let Some(_) = list.next() else {
        return Err(Error::EvalError("cdr of empty list".into()));
    };

    let rest: Vec<Value> = list.cloned().collect();
    Ok(Value::List(rest))
}

fn builtin_cons(first: Value, rest: Value) -> Result<Value, Error> {
    match rest {
        Value::List(tail) => {
            let mut new_list = vec![first];
            new_list.extend_from_slice(&tail);
            Ok(Value::List(new_list))
        }
        _ => Err(Error::TypeError(
            // SCHEME-STRICT: Require second argument to be a list (Scheme R7RS allows improper lists)
            "cons requires a list as second argument".to_owned(),
        )),
    }
}

fn builtin_list(args: ValueIter<'_>) -> Value {
    Value::List(args.cloned().collect())
}

fn builtin_null(value: Value) -> bool {
    value.is_nil()
}

fn builtin_not(b: bool) -> bool {
    !b
}

fn builtin_equal(first: Value, second: Value) -> Result<bool, Error> {
    // Scheme's equal? is structural equality for all types
    // JSONLOGIC-STRICT: Reject type coercion - require same types for equality
    match (&first, &second) {
        (Value::Bool(_), Value::Bool(_))
        | (Value::Number(_), Value::Number(_))
        | (Value::String(_), Value::String(_))
        | (Value::Symbol(_), Value::Symbol(_))
        | (Value::List(_), Value::List(_)) => {
            // Same types - use structural equality
            Ok(first == second)
        }
        _ => {
            // Different types or non-comparable types - reject type coercion
            Err(Error::TypeError(
            "JSONLOGIC-STRICT: Equality comparison requires arguments of the same comparable type (no type coercion)".to_owned(),
        ))
        }
    }
}

fn builtin_string_append(args: StringIter<'_>) -> String {
    let mut result = String::new();
    for s in args {
        result.push_str(s);
    }
    result
}

fn builtin_max(first: NumberType, rest: NumIter<'_>) -> NumberType {
    let mut result = first;
    for n in rest {
        result = result.max(n);
    }
    result
}

fn builtin_min(first: NumberType, rest: NumIter<'_>) -> NumberType {
    let mut result = first;
    for n in rest {
        result = result.min(n);
    }
    result
}

fn builtin_error(args: ValueIter<'_>) -> Result<Value, Error> {
    let parts: Vec<String> = args
        .map(|value| match value {
            Value::String(s) => s.clone(),
            _ => format!("{value}"),
        })
        .collect();

    let message = if parts.is_empty() {
        "Error".to_string()
    } else {
        parts.join(" ")
    };

    Err(Error::EvalError(message))
}

/// Global registry of all built-in operations.
///
/// We keep the registry layout as a single contiguous collection of
/// `BuiltinOp` values for ease of auditing, but the underlying
/// builtin implementations are wired through the same adapter layer
/// used for custom builtin registration. This is done once at
/// initialization time via a `LazyLock`.
static BUILTIN_OPS: LazyLock<Vec<BuiltinOp>> = LazyLock::new(|| {
    fn builtin_fixed<Args, F>(f: F) -> Arc<OperationFn>
    where
        F: IntoOperation<Args>,
    {
        <F as IntoOperation<Args>>::into_operation(f)
    }

    fn builtin_variadic<Args, F>(f: F) -> Arc<OperationFn>
    where
        F: IntoVariadicOperation<Args>,
    {
        <F as IntoVariadicOperation<Args>>::into_variadic_operation(f)
    }

    vec![
        // Arithmetic operations
        BuiltinOp {
            scheme_id: "+",
            jsonlogic_id: "+",
            op_kind: OpKind::Function(builtin_variadic::<(NumIter<'static>,), _>(builtin_add)),
            arity: Arity::AtLeast(0),
        },
        BuiltinOp {
            scheme_id: "-",
            jsonlogic_id: "-",
            op_kind: OpKind::Function(builtin_variadic::<(NumberType, NumIter<'static>), _>(
                builtin_sub,
            )),
            arity: Arity::AtLeast(1),
        },
        BuiltinOp {
            scheme_id: "*",
            jsonlogic_id: "*",
            op_kind: OpKind::Function(builtin_variadic::<(NumberType, NumIter<'static>), _>(
                builtin_mul,
            )),
            arity: Arity::AtLeast(1), // SCHEME-STRICT: Scheme R7RS allows 0 arguments (returns 1)
        },
        // Comparison operations
        BuiltinOp {
            scheme_id: ">",
            jsonlogic_id: ">",
            op_kind: OpKind::Function(builtin_variadic::<(NumberType, NumIter<'static>), _>(
                builtin_gt,
            )),
            arity: Arity::AtLeast(2),
        },
        BuiltinOp {
            scheme_id: ">=",
            jsonlogic_id: ">=",
            op_kind: OpKind::Function(builtin_variadic::<(NumberType, NumIter<'static>), _>(
                builtin_ge,
            )),
            arity: Arity::AtLeast(2),
        },
        BuiltinOp {
            scheme_id: "<",
            jsonlogic_id: "<",
            op_kind: OpKind::Function(builtin_variadic::<(NumberType, NumIter<'static>), _>(
                builtin_lt,
            )),
            arity: Arity::AtLeast(2),
        },
        BuiltinOp {
            scheme_id: "<=",
            jsonlogic_id: "<=",
            op_kind: OpKind::Function(builtin_variadic::<(NumberType, NumIter<'static>), _>(
                builtin_le,
            )),
            arity: Arity::AtLeast(2),
        },
        BuiltinOp {
            scheme_id: "=",
            jsonlogic_id: "scheme-numeric-equals",
            op_kind: OpKind::Function(builtin_variadic::<(NumberType, NumIter<'static>), _>(
                builtin_eq,
            )),
            arity: Arity::AtLeast(2),
        },
        BuiltinOp {
            scheme_id: "equal?",
            jsonlogic_id: "===",
            op_kind: OpKind::Function(builtin_fixed::<(Value, Value), _>(builtin_equal)),
            arity: Arity::Exact(2),
        },
        // Logical operations
        BuiltinOp {
            scheme_id: "not",
            jsonlogic_id: "!",
            op_kind: OpKind::Function(builtin_fixed::<(bool,), _>(builtin_not)),
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
            op_kind: OpKind::Function(builtin_fixed::<(ValueIter<'static>,), _>(builtin_car)),
            arity: Arity::Exact(1),
        },
        BuiltinOp {
            scheme_id: "cdr",
            jsonlogic_id: "scheme-cdr",
            op_kind: OpKind::Function(builtin_fixed::<(ValueIter<'static>,), _>(builtin_cdr)),
            arity: Arity::Exact(1),
        },
        BuiltinOp {
            scheme_id: "cons",
            jsonlogic_id: "scheme-cons",
            op_kind: OpKind::Function(builtin_fixed::<(Value, Value), _>(builtin_cons)),
            arity: Arity::Exact(2),
        },
        BuiltinOp {
            scheme_id: "list",
            jsonlogic_id: "scheme-list",
            op_kind: OpKind::Function(builtin_variadic::<(ValueIter<'static>,), _>(builtin_list)),
            arity: Arity::Any,
        },
        BuiltinOp {
            scheme_id: "null?",
            jsonlogic_id: "scheme-null?",
            op_kind: OpKind::Function(builtin_fixed::<(Value,), _>(builtin_null)),
            arity: Arity::Exact(1),
        },
        // String operations
        BuiltinOp {
            scheme_id: "string-append",
            jsonlogic_id: "cat",
            op_kind: OpKind::Function(builtin_variadic::<(StringIter<'static>,), _>(
                builtin_string_append,
            )),
            arity: Arity::Any,
        },
        // Math operations
        BuiltinOp {
            scheme_id: "max",
            jsonlogic_id: "max",
            op_kind: OpKind::Function(builtin_variadic::<(NumberType, NumIter<'static>), _>(
                builtin_max,
            )),
            arity: Arity::AtLeast(1),
        },
        BuiltinOp {
            scheme_id: "min",
            jsonlogic_id: "min",
            op_kind: OpKind::Function(builtin_variadic::<(NumberType, NumIter<'static>), _>(
                builtin_min,
            )),
            arity: Arity::AtLeast(1),
        },
        // Error handling
        BuiltinOp {
            scheme_id: "error",
            jsonlogic_id: "scheme-error",
            op_kind: OpKind::Function(builtin_variadic::<(ValueIter<'static>,), _>(builtin_error)),
            arity: Arity::Any,
        },
    ]
});

/// Lazy static map from scheme_id to BuiltinOp (private - use find_builtin_op_by_scheme_id)
static BUILTIN_SCHEME: LazyLock<HashMap<&'static str, &'static BuiltinOp>> = LazyLock::new(|| {
    let ops: &'static [BuiltinOp] = BUILTIN_OPS.as_slice();
    ops.iter().map(|op| (op.scheme_id, op)).collect()
});

/// Lazy static map from jsonlogic_id to BuiltinOp (private - use find_builtin_op_by_jsonlogic_id)
static BUILTIN_JSONLOGIC: LazyLock<HashMap<&'static str, &'static BuiltinOp>> =
    LazyLock::new(|| {
        let ops: &'static [BuiltinOp] = BUILTIN_OPS.as_slice();
        ops.iter().map(|op| (op.jsonlogic_id, op)).collect()
    });

/// Get all builtin operations (for internal use by evaluator)
pub(crate) fn get_builtin_ops() -> &'static [BuiltinOp] {
    BUILTIN_OPS.as_slice()
}

/// Find a builtin operation by its Scheme identifier
pub(crate) fn find_scheme_op(id: &str) -> Option<&'static BuiltinOp> {
    BUILTIN_SCHEME.get(id).copied()
}

/// Find a builtin operation by its JSONLogic identifier
pub(crate) fn find_jsonlogic_op(id: &str) -> Option<&'static BuiltinOp> {
    BUILTIN_JSONLOGIC.get(id).copied()
}

/// Get the quote builtin operation - guaranteed to exist
pub(crate) fn get_quote_op() -> &'static BuiltinOp {
    find_scheme_op("quote").expect("quote builtin operation must be available")
}

/// Get the list builtin operation - guaranteed to exist
pub(crate) fn get_list_op() -> &'static BuiltinOp {
    find_scheme_op("list").expect("list builtin operation must be available")
}

#[cfg(test)]
#[expect(clippy::unwrap_used)] // test code OK
mod tests {
    use super::*;
    use crate::ast::{nil, val};

    /// Micro-helper for success cases in comprehensive tests
    fn success<T: Into<Value>>(value: T) -> Option<Value> {
        Some(val(value))
    }

    /// Helper to invoke a builtin through the public registry using
    /// the canonical erased signature (Vec<Value> -> Result<Value, Error>).
    ///
    /// This keeps tests independent of the internal typed helper
    /// function signatures while still exercising the adapter layer.
    fn call_builtin(name: &str, args: &[Value]) -> Result<Value, Error> {
        let op = find_scheme_op(name).expect("builtin not found");
        match &op.op_kind {
            OpKind::Function(func) => func(args.to_vec()),
            OpKind::SpecialForm(_) => {
                panic!("expected function builtin in tests, got special form: {name}")
            }
        }
    }

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
            let result = func(vec![val(1), val(2)]).unwrap();
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
        assert_eq!(find_jsonlogic_op("===").unwrap().scheme_id, "equal?");
        assert_eq!(find_jsonlogic_op("+").unwrap().scheme_id, "+");

        // Scheme to JSONLogic mapping (test inline conversion)
        assert_eq!(find_scheme_op("not").unwrap().jsonlogic_id, "!");
        assert_eq!(find_scheme_op("equal?").unwrap().jsonlogic_id, "===");
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

    /// Macro to create test cases, invoking builtins via the registry.
    macro_rules! test {
        ($name:expr, $args:expr, $expected:expr) => {
            ($name, call_builtin($name, $args), $expected)
        };
    }

    #[test]
    #[expect(clippy::too_many_lines)] // Comprehensive test coverage is intentionally thorough
    fn test_builtin_function_implementations() {
        type TestCase = (&'static str, Result<Value, Error>, Option<Value>);

        // =================================================================
        // DYNAMIC TEST DATA SETUP
        // =================================================================

        // Pre-declare list for tests that need variable reuse
        let int_list = val([1, 2, 3]);

        // Arithmetic edge case data
        let many_ones: Vec<Value> = (0..100).map(|_| val(1)).collect();

        // Comparison edge case data
        let all_fives: Vec<Value> = (0..10).map(|_| val(5)).collect();
        let mut mostly_fives = all_fives.clone();
        mostly_fives.push(val(6));

        // List operations data
        let nested = val([val([val([1])])]);
        let mixed = val([val(1), val("hello"), val(true), nil()]);
        let many_elements: Vec<Value> = (0..50).map(val).collect();

        // Equality test data
        let complex1 = val([val(1), val("test"), val([val(2)])]);
        let complex2 = val([val(1), val("test"), val([val(2)])]);
        let complex3 = val([val(1), val("test"), val([val(3)])]);

        let test_cases: Vec<TestCase> = vec![
            // =================================================================
            // BASIC ARITHMETIC FUNCTIONS
            // =================================================================

            // Test arithmetic functions - addition
            test!("+", &[], success(0)),                       // Identity
            test!("+", &[val(5)], success(5)),                 // Single number
            test!("+", &[val(1), val(2), val(3)], success(6)), // Multiple numbers
            test!("+", &[val(-5), val(10)], success(5)),       // Negative numbers
            test!("+", &[val(0), val(0), val(0)], success(0)), // Zeros
            // Test addition error cases
            test!("+", &[val("not a number")], None), // Invalid type
            test!("+", &[val(1), val(true)], None),   // Mixed types
            // Test arithmetic functions - subtraction
            test!("-", &[val(5)], success(-5)), // Unary minus
            test!("-", &[val(-5)], success(5)), // Unary minus of negative
            test!("-", &[val(10), val(3), val(2)], success(5)), // Multiple subtraction
            test!("-", &[val(0), val(5)], success(-5)), // Zero minus number
            test!("-", &[val(10), val(0)], success(10)), // Number minus zero
            // Test subtraction error cases
            test!("-", &[], None), // No arguments
            test!("-", &[val("not a number")], None),
            test!("-", &[val(5), val(false)], None),
            // Test arithmetic functions - multiplication
            // SCHEME-STRICT: We require at least 1 argument (Scheme R7RS allows 0 args, returns 1)
            test!("*", &[], None),             // No arguments should error
            test!("*", &[val(5)], success(5)), // Single number
            test!("*", &[val(2), val(3), val(4)], success(24)), // Multiple numbers
            test!("*", &[val(-2), val(3)], success(-6)), // Negative numbers
            test!("*", &[val(0), val(100)], success(0)), // Zero multiplication
            test!("*", &[val(1), val(1), val(1)], success(1)), // Ones
            // Test multiplication error cases
            test!("*", &[val("not a number")], None),
            test!("*", &[val(2), nil()], None),
            // Test comparison functions - greater than
            test!(">", &[val(7), val(3)], success(true)),
            test!(">", &[val(3), val(8)], success(false)),
            test!(">", &[val(4), val(4)], success(false)), // Equal case
            test!(">", &[val(-1), val(-2)], success(true)), // Negative numbers
            // Test chaining behavior: 9 > 6 > 2 should be true since all adjacent pairs satisfy >
            test!(">", &[val(9), val(6), val(2)], success(true)), // Chaining true
            // Test chaining that should fail: 9 > 6 > 7 should be false since 6 > 7 is false
            test!(">", &[val(9), val(6), val(7)], success(false)), // Chaining false
            // Test comparison error cases (wrong number of args or wrong types)
            test!(">", &[val(5)], None),           // Too few args
            test!(">", &[val("a"), val(3)], None), // Wrong type
            // Test comparison functions - greater than or equal
            test!(">=", &[val(8), val(3)], success(true)),
            test!(">=", &[val(2), val(6)], success(false)),
            test!(">=", &[val(7), val(7)], success(true)), // Equal case
            // Test comparison functions - less than
            test!("<", &[val(2), val(9)], success(true)),
            test!("<", &[val(8), val(4)], success(false)),
            test!("<", &[val(6), val(6)], success(false)), // Equal case
            // Test numeric comparison chaining: 1 < 2 < 3 (all adjacent pairs satisfy <)
            test!("<", &[val(1), val(2), val(3)], success(true)), // Chaining true
            // Test chaining that should fail: 1 < 3 but not 3 < 2
            test!("<", &[val(1), val(3), val(2)], success(false)), // Chaining false
            // Test comparison functions - less than or equal
            test!("<=", &[val(4), val(9)], success(true)),
            test!("<=", &[val(8), val(2)], success(false)),
            test!("<=", &[val(3), val(3)], success(true)), // Equal case
            // Test numeric equality
            test!("=", &[val(12), val(12)], success(true)),
            test!("=", &[val(8), val(3)], success(false)),
            test!("=", &[val(0), val(0)], success(true)),
            test!("=", &[val(-1), val(-1)], success(true)),
            test!("=", &[val(7), val(7), val(7)], success(true)), // 7 = 7 = 7 (all equal)
            test!("=", &[val(9), val(9), val(4)], success(false)), // 9 = 9 but not 9 = 4
            // Test structural equality (equal?)
            test!("equal?", &[val(11), val(11)], success(true)),
            test!("equal?", &[val(15), val(3)], success(false)),
            test!("equal?", &[val("hello"), val("hello")], success(true)),
            test!("equal?", &[val("hello"), val("world")], success(false)),
            test!("equal?", &[val(true), val(true)], success(true)),
            test!("equal?", &[val(true), val(false)], success(false)),
            test!("equal?", &[nil(), nil()], success(true)),
            test!("equal?", &[val([1]), val([1])], success(true)),
            test!("equal?", &[val(5), val("5")], None), // Different types - now rejected
            // Test equal? error cases (structural equality requires exactly 2 args)
            test!("equal?", &[val(5)], None), // Too few args
            test!("equal?", &[val(5), val(3), val(1)], None), // Too many args
            // Test logical functions - not
            test!("not", &[val(true)], success(false)),
            test!("not", &[val(false)], success(true)),
            // Test not error cases
            test!("not", &[], None),                      // No args
            test!("not", &[val(true), val(false)], None), // Too many args
            test!("not", &[val(1)], None),                // Wrong type
            test!("not", &[val("true")], None),           // Wrong type
            // Test list functions - car
            test!("car", &[val([1, 2, 3])], success(1)), // First element
            test!("car", &[val(["only"])], success("only")), // Single element
            test!("car", &[val([val([1]), val(2)])], success([1])), // Nested list
            // Test car error cases
            test!("car", &[], None), // No args
            test!("car", &[int_list.clone(), int_list.clone()], None), // Too many args
            test!("car", &[nil()], None), // Empty list
            test!("car", &[val(42)], None), // Not a list
            test!("car", &[val("not a list")], None), // Not a list
            // Test list functions - cdr
            test!("cdr", &[val([1, 2, 3])], success([2, 3])), // Rest of list
            test!("cdr", &[val(["only"])], Some(nil())),      // Single element -> empty
            test!("cdr", &[val([1, 2])], success([2])),       // Two elements
            // Test cdr error cases
            test!("cdr", &[], None),                           // No args
            test!("cdr", &[int_list.clone(), int_list], None), // Too many args
            test!("cdr", &[nil()], None),                      // Empty list
            test!("cdr", &[val(true)], None),                  // Not a list
            // Test list functions - cons
            test!("cons", &[val(0), val([1, 2])], success([0, 1, 2])), // Prepend to list
            test!("cons", &[val("first"), nil()], success(["first"])), // Cons to empty
            test!("cons", &[val([1]), val([2])], success([val([1]), val(2)])), // Nested cons
            // Test cons error cases
            test!("cons", &[], None),                          // No args
            test!("cons", &[val(1)], None),                    // Too few args
            test!("cons", &[val(1), val(2), val(3)], None),    // Too many args
            test!("cons", &[val(1), val(2)], None),            // Second arg not a list
            test!("cons", &[val(1), val("not a list")], None), // Second arg not a list
            // Test list functions - list
            test!("list", &[], Some(nil())),        // Empty list
            test!("list", &[val(1)], success([1])), // Single element
            test!(
                "list",
                &[val(1), val("hello"), val(true)],
                success([val(1), val("hello"), val(true)])
            ), // Mixed types
            test!("list", &[val([1]), val(2)], success([val([1]), val(2)])), // Nested lists
            // Test null? function
            test!("null?", &[nil()], success(true)), // Empty list is nil
            test!("null?", &[val(42)], success(false)), // Number is not nil
            test!("null?", &[val("")], success(false)), // Empty string is not nil
            test!("null?", &[val(false)], success(false)), // False is not nil
            test!("null?", &[val([1])], success(false)), // Non-empty list is not nil
            // Test null? error cases
            test!("null?", &[], None),               // No args
            test!("null?", &[val(1), val(2)], None), // Too many args
            // Test error function
            test!("error", &[], None), // No args - should produce generic error
            test!("error", &[val("test error")], None), // String message
            test!("error", &[val(42)], None), // Number message
            test!("error", &[val(true)], None), // Bool message
            test!("error", &[val("Error:"), val("Something went wrong")], None), // Multiple args
            // =================================================================
            // ARITHMETIC EDGE CASES
            // =================================================================

            // Integer overflow cases (should fail)
            test!("+", &[val(NumberType::MAX), val(1)], None), // Addition overflow
            test!("*", &[val(NumberType::MAX), val(2)], None), // Multiplication overflow
            test!("-", &[val(NumberType::MIN)], None),         // Negation overflow
            test!("-", &[val(NumberType::MIN), val(1)], None), // Subtraction overflow
            // Boundary values (should succeed)
            test!(
                "+",
                &[val(NumberType::MAX), val(0)],
                success(NumberType::MAX)
            ),
            test!(
                "-",
                &[val(NumberType::MIN), val(0)],
                success(NumberType::MIN)
            ),
            test!(
                "*",
                &[val(NumberType::MAX), val(1)],
                success(NumberType::MAX)
            ),
            test!("*", &[val(0), val(NumberType::MAX)], success(0)),
            // Operations with zero
            test!("+", &[val(0)], success(0)),
            test!("-", &[val(0)], success(0)),
            test!("*", &[val(0)], success(0)),
            // Large chain operations
            test!("+", &many_ones, success(100)),
            test!("*", &many_ones, success(1)),
            // =================================================================
            // COMPARISON EDGE CASES
            // =================================================================

            // Boundary comparisons
            test!(
                ">",
                &[val(NumberType::MAX), val(NumberType::MIN)],
                success(true)
            ),
            test!(
                "<",
                &[val(NumberType::MIN), val(NumberType::MAX)],
                success(true)
            ),
            test!(
                ">=",
                &[val(NumberType::MAX), val(NumberType::MAX)],
                success(true)
            ),
            test!(
                "<=",
                &[val(NumberType::MIN), val(NumberType::MIN)],
                success(true)
            ),
            // Long chain comparisons
            test!(
                "<",
                &[val(-5), val(-2), val(0), val(3), val(10)],
                success(true)
            ),
            test!(
                ">",
                &[val(10), val(5), val(0), val(-3), val(-8)],
                success(true)
            ),
            test!("<", &[val(1), val(2), val(1)], success(false)), // 2 > 1 fails
            // Numeric equality with many values
            test!("=", &all_fives, success(true)),
            test!("=", &mostly_fives, success(false)),
            // =================================================================
            // LIST OPERATIONS EDGE CASES
            // =================================================================

            // Deeply nested lists
            test!("car", &[nested], success([val([1])])),
            // Mixed type lists operations
            test!("car", std::slice::from_ref(&mixed), success(1)),
            test!(
                "cdr",
                std::slice::from_ref(&mixed),
                success([val("hello"), val(true), nil()])
            ),
            // Cons with various types
            test!(
                "cons",
                &[val(true), val([val(1), val(2)])],
                success([val(true), val(1), val(2)])
            ),
            // List creation with many elements
            test!(
                "list",
                &many_elements,
                success((0..50).map(val).collect::<Vec<_>>())
            ),
            // =================================================================
            // STRING OPERATIONS
            // =================================================================

            // Basic string concatenation
            test!("string-append", &[], success("")),
            test!("string-append", &[val("hello")], success("hello")),
            test!(
                "string-append",
                &[val("hello"), val(" "), val("world")],
                success("hello world")
            ),
            test!(
                "string-append",
                &[val(""), val("test"), val("")],
                success("test")
            ),
            // Error cases - non-string arguments
            test!("string-append", &[val(42)], None),
            test!("string-append", &[val("hello"), val(123)], None),
            test!("string-append", &[val(true), val("world")], None),
            // =================================================================
            // MATH OPERATIONS - MAX/MIN
            // =================================================================

            // Basic max operations
            test!("max", &[val(5)], success(5)),
            test!("max", &[val(1), val(2), val(3)], success(3)),
            test!("max", &[val(3), val(1), val(2)], success(3)),
            test!("max", &[val(-5), val(-1), val(-10)], success(-1)),
            // Basic min operations
            test!("min", &[val(5)], success(5)),
            test!("min", &[val(1), val(2), val(3)], success(1)),
            test!("min", &[val(3), val(1), val(2)], success(1)),
            test!("min", &[val(-5), val(-1), val(-10)], success(-10)),
            // Error cases - no arguments
            test!("max", &[], None),
            test!("min", &[], None),
            // Error cases - non-number arguments
            test!("max", &[val("hello")], None),
            test!("min", &[val(true)], None),
            test!("max", &[val(1), val("hello")], None),
            test!("min", &[val(1), val(true)], None),
            // =================================================================
            // EQUALITY STRICT TYPING - OVERRIDE BASIC EQUAL TESTS
            // =================================================================

            // Type coercion rejection (these should fail)
            test!("equal?", &[val(1), val("1")], None),
            test!("equal?", &[val(0), val(false)], None),
            test!("equal?", &[val(true), val(1)], None),
            test!("equal?", &[val(""), nil()], None),
            test!("equal?", &[val(Vec::<Value>::new()), val(false)], None),
            // Complex same-type structures
            test!("equal?", &[complex1.clone(), complex2], success(true)),
            test!("equal?", &[complex1, complex3], success(false)),
            // =================================================================
            // LOGICAL OPERATIONS STRICT - ADDITIONAL ERROR CASES
            // =================================================================

            // Non-boolean inputs should fail
            test!("not", &[val(0)], None),
            test!("not", &[val("")], None),
            test!("not", &[nil()], None),
            test!("not", &[val("false")], None),
        ];

        for (test_expr, result, expected) in test_cases {
            match (result, expected) {
                (Ok(actual), Some(expected_val)) => {
                    assert_eq!(actual, expected_val, "Failed for test case: {test_expr}");
                }
                (Err(_), None) => {} // Expected error
                (actual, expected) => panic!(
                    "Unexpected result for test case: {}\nGot result: {:?}, Expected: {:?}",
                    test_expr,
                    actual.is_ok(),
                    expected.is_some()
                ),
            }
        }
    }

    #[test]
    fn test_error_message_construction() {
        type ErrorTest = (Vec<Value>, &'static str);
        let test_cases: Vec<ErrorTest> = vec![
            (vec![val("Simple message")], "Simple message"),
            (
                vec![val("Code:"), val(404), val("Not Found")],
                "Code: 404 Not Found",
            ),
            (
                vec![val(true), val(42), val("mixed"), nil()],
                "#t 42 mixed ()",
            ),
        ];

        for (args, expected_msg) in test_cases {
            match call_builtin("error", &args).unwrap_err() {
                Error::EvalError(msg) => {
                    assert_eq!(msg, expected_msg, "Failed for args: {args:?}");
                }
                _ => panic!("Expected EvalError for args: {args:?}"),
            }
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
            Error::ArityError { expected, got, .. } => {
                assert_eq!(expected, 2);
                assert_eq!(got, 1);
            }
            _ => panic!("Expected ArityError"),
        }
    }
}
