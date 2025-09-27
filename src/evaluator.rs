use crate::SchemeError;
use crate::ast::{Value, nil, sym, unspecified, val};
use crate::builtinops::get_builtin_ops;
use std::collections::HashMap;

/// Environment for variable bindings
#[derive(Debug, Clone, PartialEq, Default)]
pub struct Environment {
    bindings: HashMap<String, Value>,
    parent: Option<Box<Environment>>,
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

/// Evaluate an S-expression in the given environment
pub fn eval(expr: &Value, env: &mut Environment) -> Result<Value, SchemeError> {
    match expr {
        // Self-evaluating forms (empty lists are NOT self-evaluating for strict semantics)
        Value::Number(_)
        | Value::String(_)
        | Value::Bool(_)
        | Value::BuiltinFunction { .. }
        | Value::Function { .. }
        | Value::Unspecified => Ok(expr.clone()),

        // Variable lookup
        Value::Symbol(name) => env
            .get(name)
            .cloned()
            .ok_or_else(|| SchemeError::UnboundVariable(name.clone())),

        // PrecompiledOp evaluation (optimized path for builtin operations and special forms)
        // This is where special forms are actually handled - they are converted to PrecompiledOps
        // during parsing since they are syntax structures, not dynamic function calls.
        // Note: Arity is already validated at parse time, so no runtime checking needed
        Value::PrecompiledOp { op, args, .. } => {
            use crate::builtinops::OpKind;
            match &op.op_kind {
                OpKind::Function(f) => {
                    // Evaluate all arguments using helper function
                    let evaluated_args = eval_args(args, env)?;
                    // Apply the function (arity already validated at parse time)
                    f(&evaluated_args)
                }
                OpKind::SpecialForm(special_form) => {
                    // Special forms are syntax structures handled here after being converted
                    // to PrecompiledOps during parsing. They get unevaluated arguments.
                    // (arity already validated at parse time)
                    special_form(args, env)
                }
            }
        }

        // List evaluation (function application or special forms)
        Value::List(elements) => eval_list(elements, env).map_err(|err| add_context(err, expr)),
    }
}

/// Helper function to add expression context to errors
fn add_context(error: SchemeError, expr: &Value) -> SchemeError {
    let context = format!("while evaluating: {}", expr);
    match error {
        SchemeError::EvalError(msg) => {
            SchemeError::EvalError(format!("{}\n  Context: {}", msg, context))
        }
        SchemeError::TypeError(msg) => {
            SchemeError::TypeError(format!("{}\n  Context: {}", msg, context))
        }
        _ => error, // Don't add context to parse errors, unbound variables, or arity errors (they have their own context)
    }
}

/// Helper function to evaluate a list of argument expressions
fn eval_args(args: &[Value], env: &mut Environment) -> Result<Vec<Value>, SchemeError> {
    let mut evaluated_args = Vec::new();
    for arg_expr in args {
        evaluated_args.push(eval(arg_expr, env)?);
    }
    Ok(evaluated_args)
}

/// Evaluate a list expression (function application)
///
/// Note: Both builtin functions and special forms are converted to PrecompiledOps
/// during parsing for optimization. Special forms are syntax structures that cannot
/// be dynamically generated, while builtin functions benefit from pre-validation.
/// All PrecompiledOps are handled in the main eval() function. Therefore, eval_list()
/// only needs to handle dynamic function application cases.
///
/// If the PrecompiledOps optimization were removed, special forms would need
/// special handling here. Builtin functions are added to the environment and
/// can be called dynamically through normal symbol lookup and function application.
fn eval_list(elements: &[Value], env: &mut Environment) -> Result<Value, SchemeError> {
    // Note: Dynamic calls (not PrecompiledOps) still need runtime arity checking
    match elements {
        [] => Err(SchemeError::EvalError(
            "Cannot evaluate empty list".to_string(),
        )),

        // Function application: evaluate function expression, then apply to arguments
        // Note: If PrecompiledOps optimization were removed, we would need to check for
        // special forms here before function application (builtin functions work via symbol lookup)
        [func_expr, arg_exprs @ ..] => {
            // Evaluate the function
            let func = eval(func_expr, env)?;

            // Evaluate the arguments
            let args = eval_args(arg_exprs, env)?;

            // Apply the function
            match &func {
                // Dynamic function calls
                Value::BuiltinFunction { func: f, .. } => f(&args),
                Value::Function {
                    params,
                    body,
                    env: closure_env,
                } => {
                    if params.len() != args.len() {
                        return Err(SchemeError::arity_error(params.len(), args.len()));
                    }

                    // Create new environment with closure environment as parent
                    let mut new_env = Environment::with_parent(closure_env.clone());

                    // Bind parameters to arguments
                    for (param, arg) in params.iter().zip(args.iter()) {
                        new_env.define(param.clone(), arg.clone());
                    }

                    // Evaluate body with context
                    eval(body, &mut new_env).map_err(|err| match err {
                        SchemeError::EvalError(msg) => {
                            SchemeError::EvalError(format!("{}\n  In lambda: {}", msg, body))
                        }
                        SchemeError::TypeError(msg) => {
                            SchemeError::TypeError(format!("{}\n  In lambda: {}", msg, body))
                        }
                        other => other,
                    })
                }
                _ => Err(SchemeError::TypeError(format!(
                    "Cannot apply non-function: {}",
                    func
                ))),
            }
        }
    }
}

/// Evaluate quote special form
pub fn eval_quote(args: &[Value], _env: &mut Environment) -> Result<Value, SchemeError> {
    match args {
        [expr] => Ok(expr.clone()), // Quote content is already unoptimized during parsing
        _ => Err(SchemeError::arity_error(1, args.len())),
    }
}

/// Evaluate define special form
pub fn eval_define(args: &[Value], env: &mut Environment) -> Result<Value, SchemeError> {
    match args {
        [Value::Symbol(name), expr] => {
            let value = eval(expr, env)?;
            env.define(name.clone(), value.clone());
            Ok(unspecified())
        }
        [_, _] => Err(SchemeError::TypeError(
            "define requires a symbol".to_string(),
        )),
        _ => Err(SchemeError::arity_error(2, args.len())),
    }
}

/// Evaluate if special form
pub fn eval_if(args: &[Value], env: &mut Environment) -> Result<Value, SchemeError> {
    match args {
        [condition_expr, then_expr, else_expr] => {
            let condition = eval(condition_expr, env)?;
            match condition {
                Value::Bool(true) => eval(then_expr, env),
                Value::Bool(false) => eval(else_expr, env),
                _ => Err(SchemeError::TypeError(
                    "SCHEME-JSONLOGIC-STRICT: if condition must be a boolean".to_string(),
                )),
            }
        }
        _ => Err(SchemeError::arity_error(3, args.len())),
    }
}

/// Evaluate lambda special form
pub fn eval_lambda(args: &[Value], env: &mut Environment) -> Result<Value, SchemeError> {
    match args {
        [Value::List(param_list), body] => {
            let mut params = Vec::new();
            for param in param_list {
                match param {
                    Value::Symbol(name) => {
                        // Check for duplicate parameter names (R7RS compliant)
                        if params.contains(name) {
                            return Err(SchemeError::EvalError(format!(
                                "Duplicate parameter name: {}",
                                name
                            )));
                        }
                        params.push(name.clone());
                    }
                    _ => {
                        return Err(SchemeError::TypeError(
                            "Lambda parameters must be symbols".to_string(),
                        ));
                    }
                }
            }

            // SCHEME-STRICT: We do not support Scheme's variadic lambda forms:
            // - (lambda args body) - where args is a symbol that collects all arguments as a list
            // - (lambda (a b . rest) body) - where rest collects remaining arguments (dot notation)
            // Our implementation only supports fixed-arity lambdas with explicit parameter lists.

            Ok(Value::Function {
                params,
                body: Box::new(body.clone()),
                env: env.clone(),
            })
        }
        [_, _] => Err(SchemeError::TypeError(
            "Lambda parameters must be a list".to_string(),
        )),
        _ => Err(SchemeError::arity_error(2, args.len())),
    }
}

/// Check if a value is obviously non-boolean (before evaluation)
/// This catches literals and some obvious cases, but can't check function call results
fn is_obviously_non_boolean(value: &Value) -> bool {
    match value {
        Value::Bool(_) => false,                               // Obviously boolean
        Value::Number(_) | Value::String(_) => true,           // Obviously non-boolean
        Value::List(_) | Value::PrecompiledOp { .. } => false, // Could be function calls that return booleans
        Value::Symbol(_) => false,                             // Could be a boolean variable
        Value::Unspecified => true,                            // Obviously non-boolean
        Value::BuiltinFunction { .. } | Value::Function { .. } => false, // Functions could return booleans
    }
}

/// Evaluate and special form (strict boolean evaluation)
pub fn eval_and(args: &[Value], env: &mut Environment) -> Result<Value, SchemeError> {
    // SCHEME-STRICT: Require at least 1 argument (Scheme R7RS allows 0 args, returns #t)
    if args.is_empty() {
        return Err(SchemeError::arity_error(1, 0));
    }

    // First pass: check for obviously non-boolean arguments before evaluation, so that short-circuit evaluation doesn't hide gross errors
    for arg in args.iter() {
        if is_obviously_non_boolean(arg) {
            return Err(SchemeError::TypeError(
                "SCHEME-JSONLOGIC-STRICT: 'and' requires boolean arguments (no truthiness)"
                    .to_string(),
            ));
        }
    }

    // Second pass: evaluate each argument and require it to be a boolean
    for arg in args.iter() {
        let result = eval(arg, env)?;

        match result {
            Value::Bool(false) => return Ok(Value::Bool(false)),
            Value::Bool(true) => continue,
            _ => {
                return Err(SchemeError::TypeError(
                    "SCHEME-JSONLOGIC-STRICT: 'and' requires boolean arguments (no truthiness)"
                        .to_string(),
                ));
            }
        }
    }

    // All arguments were true
    Ok(Value::Bool(true))
}

/// Evaluate or special form (strict boolean evaluation)
pub fn eval_or(args: &[Value], env: &mut Environment) -> Result<Value, SchemeError> {
    // SCHEME-STRICT: Require at least 1 argument (Scheme R7RS allows 0 args, returns #f)
    if args.is_empty() {
        return Err(SchemeError::arity_error(1, 0));
    }

    // First pass: check for obviously non-boolean arguments before evaluation, so that short-circuit evaluation doesn't hide gross errors

    for arg in args.iter() {
        if is_obviously_non_boolean(arg) {
            return Err(SchemeError::TypeError(
                "SCHEME-JSONLOGIC-STRICT: 'or' requires boolean arguments (no truthiness)"
                    .to_string(),
            ));
        }
    }

    // Second pass: evaluate each argument and require it to be a boolean
    for arg in args {
        let result = eval(arg, env)?;

        match result {
            Value::Bool(true) => return Ok(Value::Bool(true)),
            Value::Bool(false) => continue,
            _ => {
                return Err(SchemeError::TypeError(
                    "SCHEME-JSONLOGIC-STRICT: 'or' requires boolean arguments (no truthiness)"
                        .to_string(),
                ));
            }
        }
    }

    // All arguments were false
    Ok(Value::Bool(false))
}

/// Create a global environment with built-in functions
pub fn create_global_env() -> Environment {
    let mut env = Environment::new();

    // Add all regular functions from the registry
    for builtin_op in get_builtin_ops().iter() {
        if let crate::builtinops::OpKind::Function(func) = &builtin_op.op_kind {
            // Use BuiltinFunction for environment bindings (dynamic calls through symbols)
            env.define(
                builtin_op.scheme_id.to_string(),
                Value::BuiltinFunction {
                    id: builtin_op.scheme_id.to_string(),
                    func: *func,
                },
            );
        }
    }

    env
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse;

    fn eval_string(input: &str) -> Result<Value, SchemeError> {
        let expr = parse(input)?;
        let mut env = create_global_env();
        eval(&expr, &mut env)
    }

    /// Micro-helper for success cases in comprehensive tests
    fn success<T: Into<Value>>(value: T) -> Option<Value> {
        Some(val(value))
    }

    /// Helper function to run comprehensive tests with success/failure cases
    fn run_comprehensive_tests(test_cases: Vec<(&str, Option<Value>)>) {
        for (i, (input, expected)) in test_cases.iter().enumerate() {
            let result = eval_string(input);
            match (result, expected) {
                (Ok(actual), Some(exp)) if actual == *exp => {} // Pass
                (Err(_), None) => {}                            // Expected error - pass
                (Ok(actual), Some(exp)) => {
                    panic!("#{}: expected {:?}, got {:?}", i + 1, exp, actual)
                }
                (Ok(actual), None) => panic!("#{}: should fail, got {:?}", i + 1, actual),
                (Err(err), Some(exp)) => {
                    panic!("#{}: expected {:?}, got error {:?}", i + 1, exp, err)
                }
            }
        }
    }

    #[test]
    fn test_comprehensive_operations_data_driven() {
        let test_cases = vec![
            // === SELF-EVALUATING FORMS ===
            // Numbers
            ("42", success(42)),
            ("-271", success(-271)),
            ("0", success(0)),
            ("9223372036854775807", success(i64::MAX)),
            ("-9223372036854775808", success(i64::MIN)),
            // Booleans
            ("#t", success(true)),
            ("#f", success(false)),
            // Strings
            ("\"hello\"", success("hello")),
            ("\"hello world\"", success("hello world")),
            ("\"\"", success("")),
            ("\"with\\\"quotes\"", success("with\"quotes")),
            // === ARITHMETIC OPERATIONS ===
            // Addition (allows 0 arguments - returns 0)
            ("(+ 1 2 3)", success(6)),
            ("(+ 0)", success(0)),
            ("(+ 42)", success(42)),
            ("(+ -5 10)", success(5)),
            ("(+)", success(0)), // Addition with no args returns 0
            // Subtraction (requires at least 1 argument)
            ("(- 10 3 2)", success(5)),
            ("(- 10)", success(-10)), // Unary negation
            ("(- 0)", success(0)),
            ("(- -5)", success(5)),
            ("(- 100 50 25)", success(25)),
            // Multiplication (requires at least 1 argument)
            ("(* 2 3 4)", success(24)),
            ("(* 0 100)", success(0)),
            ("(* 1)", success(1)),
            ("(* -2 3)", success(-6)),
            ("(* 7)", success(7)), // Single argument returns itself
            // Mixed operations with nested expressions
            ("(+ (* 2 3) (- 8 2))", success(12)),
            ("(* (+ 1 2) (- 5 2))", success(9)),
            ("(- (+ 10 5) (* 2 3))", success(9)),
            // Arithmetic overflow errors
            ("(+ 9223372036854775807 1)", None),  // i64::MAX + 1
            ("(- -9223372036854775808)", None),   // -(i64::MIN)
            ("(- -9223372036854775808 1)", None), // i64::MIN - 1
            ("(* 4611686018427387904 2)", None),  // (i64::MAX/2 + 1) * 2
            // === EQUALITY AND COMPARISON OPERATIONS ===
            // Numeric equality (spec-compliant - only accepts numbers)
            ("(= 5 5)", success(true)),
            ("(= 5 6)", success(false)),
            ("(= 0 0)", success(true)),
            ("(= -1 -1)", success(true)),
            ("(= 100 200)", success(false)),
            // = rejects non-numbers (type errors)
            ("(= \"hello\" \"hello\")", None),
            ("(= #t #t)", None),
            ("(= #f #f)", None),
            // General equality with equal? (works for all types)
            ("(equal? 5 5)", success(true)),
            ("(equal? 5 6)", success(false)),
            ("(equal? \"hello\" \"hello\")", success(true)),
            ("(equal? \"hello\" \"world\")", success(false)),
            ("(equal? #t #t)", success(true)),
            ("(equal? #t #f)", success(false)),
            ("(equal? #f #f)", success(true)),
            // Numeric comparison operators
            ("(< 3 5)", success(true)),
            ("(< 5 3)", success(false)),
            ("(< 0 1)", success(true)),
            ("(< -5 -3)", success(true)),
            ("(> 5 3)", success(true)),
            ("(> 3 5)", success(false)),
            ("(> 1 0)", success(true)),
            ("(> -3 -5)", success(true)),
            ("(<= 3 5)", success(true)),
            ("(<= 5 5)", success(true)),
            ("(<= 5 3)", success(false)),
            ("(<= 0 0)", success(true)),
            ("(>= 5 3)", success(true)),
            ("(>= 5 5)", success(true)),
            ("(>= 3 5)", success(false)),
            ("(>= 0 0)", success(true)),
            // === QUOTE OPERATIONS ===
            // Longhand quote syntax
            ("(quote hello)", success(sym("hello"))),
            ("(quote foo)", success(sym("foo"))),
            ("(quote (1 2 3))", success([1, 2, 3])),
            ("(quote (+ 1 2))", success([sym("+"), val(1), val(2)])),
            ("(quote (a b c))", success([sym("a"), sym("b"), sym("c")])),
            ("(quote ())", success(nil())), // Empty list (nil)
            // Shorthand quote syntax
            ("'hello", success(sym("hello"))),
            ("'(1 2 3)", success([1, 2, 3])),
            ("'(+ 1 2)", success([sym("+"), val(1), val(2)])),
            ("'()", success(nil())), // Empty list (nil) via shorthand
            ("'42", success(42)),
            ("'#t", success(true)),
            // Nested quotes
            ("'(quote x)", success([sym("quote"), sym("x")])),
            ("''x", success([sym("quote"), sym("x")])),
            // === LIST OPERATIONS ===
            // Basic list access
            ("(car (list 1 2 3))", success(1)),
            ("(car (list \"first\" \"second\"))", success("first")),
            ("(cdr (list 1 2 3))", success([2, 3])),
            ("(cdr (list \"a\" \"b\" \"c\"))", success(["b", "c"])),
            // List construction
            ("(cons 1 (list 2 3))", success([1, 2, 3])),
            ("(cons \"x\" (list \"y\" \"z\"))", success(["x", "y", "z"])),
            ("(list)", success(nil())),
            ("(list 1)", success([1])),
            ("(list 1 2 3 4)", success([1, 2, 3, 4])),
            // === CONDITIONAL OPERATIONS ===
            // Basic if expressions
            ("(if #t 1 2)", success(1)),
            ("(if #f 1 2)", success(2)),
            ("(if #t \"yes\" \"no\")", success("yes")),
            ("(if #f \"yes\" \"no\")", success("no")),
            // if with computed conditions
            ("(if (> 5 3) \"greater\" \"lesser\")", success("greater")),
            ("(if (< 5 3) \"greater\" \"lesser\")", success("lesser")),
            ("(if (equal? 1 1) 42 0)", success(42)),
            // SCHEME-JSONLOGIC-STRICT: if condition must be a boolean (rejects truthy/falsy)
            ("(if 0 1 2)", None),
            ("(if 42 1 2)", None),
            ("(if () 1 2)", None),
            ("(if \"hello\" 1 2)", None),
            // SCHEME-JSONLOGIC-STRICT: Require exactly 3 arguments
            // (Scheme allows 2 args with undefined behavior, JSONLogic allows chaining with >3 args)
            ("(if #t 1)", None),
            ("(if #f 1)", None),
            ("(if #t)", None),
            // === BOOLEAN LOGIC OPERATIONS ===
            // and operator - SCHEME-STRICT: Require at least 1 argument (Scheme R7RS allows 0 args, returns #t)
            ("(and #t)", success(true)),
            ("(and #f)", success(false)),
            ("(and #t #t)", success(true)),
            ("(and #t #f)", success(false)),
            ("(and #f #t)", success(false)),
            ("(and #t #t #t)", success(true)),
            ("(and #t #t #f)", success(false)),
            // and errors - SCHEME-JSONLOGIC-STRICT: and requires boolean arguments
            ("(and)", None),        // requires at least 1 argument
            ("(and 1 2 3)", None),  // rejects non-booleans
            ("(and 1 #f 3)", None), // rejects non-booleans
            // or operator - SCHEME-STRICT: Require at least 1 argument (Scheme R7RS allows 0 args, returns #f)
            ("(or #t)", success(true)),
            ("(or #f)", success(false)),
            ("(or #t #f)", success(true)),
            ("(or #f #t)", success(true)),
            ("(or #f #f)", success(false)),
            ("(or #f #f #t)", success(true)),
            ("(or #f #f #f)", success(false)),
            // or errors - SCHEME-JSONLOGIC-STRICT: or requires boolean arguments
            ("(or)", None),        // requires at least 1 argument
            ("(or #f 2 3)", None), // rejects non-booleans
            ("(or 1 2 3)", None),  // rejects non-booleans
            // not operator (requires exactly 1 boolean argument)
            ("(not #t)", success(false)),
            ("(not #f)", success(true)),
            // not errors - SCHEME-JSONLOGIC-STRICT: not requires boolean arguments
            ("(not ())", None),        // rejects non-booleans
            ("(not 0)", None),         // rejects non-booleans
            ("(not 42)", None),        // rejects non-booleans
            ("(not \"hello\")", None), // rejects non-booleans
            // Complex boolean expressions
            ("(and (or #f #t) (not #f))", success(true)),
            ("(or (and #f #t) (not #f))", success(true)),
            ("(not (and #t #f))", success(true)),
            ("(and (> 5 3) (< 2 4))", success(true)),
            ("(or (= 1 2) (= 2 2))", success(true)),
            // Short-circuit evaluation - undefined variables not evaluated due to short-circuit
            ("(and #f undefined-var)", success(false)), // should not evaluate undefined-var
            ("(or #t undefined-var)", success(true)),   // should not evaluate undefined-var
            // === STRICT EVALUATION SEMANTICS ===
            // SCHEME-STRICT: Empty list () is NOT self-evaluating (must be quoted)
            // This is stricter than standard Scheme but more predictable
            ("()", None), // Empty list should error when evaluated directly
            // SCHEME-STRICT: if condition must be boolean (rejects truthy/falsy including nil)
            ("(if '() 1 2)", None), // nil as condition should error
            // null? function works with quoted empty lists
            ("(null? '())", success(true)),
            ("(null? (list 1))", success(false)),
        ];

        run_comprehensive_tests(test_cases);
    }

    #[test]
    fn test_define_and_lookup() {
        let mut env = create_global_env();
        let define_expr = parse("(define x 42)").unwrap();
        eval(&define_expr, &mut env).unwrap();

        let lookup_expr = parse("x").unwrap();
        assert_eq!(eval(&lookup_expr, &mut env).unwrap(), val(42));
    }

    #[test]
    fn test_define_returns_unspecified() {
        let mut env = create_global_env();
        let define_expr = parse("(define x 42)").unwrap();
        let result = eval(&define_expr, &mut env).unwrap();

        // Define should return Unspecified
        assert!(matches!(result, Value::Unspecified));

        // Unspecified should not equal itself or any other value
        assert_ne!(result, result);
        assert_ne!(result, Value::Unspecified);
        assert_ne!(result, unspecified());
        assert_ne!(result, val(42));
        assert_ne!(result, val(true));
    }

    #[test]
    fn test_error_function() {
        // Test error with string message
        let result = eval_string("(error \"Something went wrong\")");
        assert!(result.is_err());
        if let Err(SchemeError::EvalError(msg)) = result {
            assert!(msg.contains("Something went wrong"));
        }

        // Test error with symbol message
        let result = eval_string("(error oops)");
        assert!(result.is_err());
        if let Err(SchemeError::EvalError(msg)) = result {
            assert!(msg.contains("oops"));
        }

        // Test error with number message
        let result = eval_string("(error 42)");
        assert!(result.is_err());
        if let Err(SchemeError::EvalError(msg)) = result {
            assert!(msg.contains("42"));
        }

        // Test error with multiple arguments
        let result = eval_string("(error \"Error:\" 42 \"occurred\")");
        assert!(result.is_err());
        if let Err(SchemeError::EvalError(msg)) = result {
            assert!(msg.contains("Error: 42 occurred"));
        }

        // Test error with no arguments
        let result = eval_string("(error)");
        assert!(result.is_err());
        if let Err(SchemeError::EvalError(msg)) = result {
            assert!(msg.contains("Error"));
        }
    }

    /// Comprehensive tests to ensure all evaluation paths work correctly
    /// and that PrecompiledOps never escape as first-class values
    mod evaluation_paths {
        use super::*;

        #[test]
        fn test_precompiled_ops_are_consumed_not_produced() {
            // PrecompiledOps should be created during parsing and consumed during evaluation
            // They should never be returned as values from evaluation

            // Test that builtin operations are PrecompiledOps during parsing but return concrete values
            let expr = parse("(+ 1 2)").unwrap();
            match &expr {
                Value::PrecompiledOp { .. } => {} // Good - parsed as PrecompiledOp
                _ => panic!("Expected PrecompiledOp from parsing"),
            }

            // But evaluation should return a concrete value, never PrecompiledOp
            let result = eval_string("(+ 1 2)").unwrap();
            match result {
                Value::Number(3) => {} // Good - concrete value
                Value::PrecompiledOp { .. } => {
                    panic!("eval() returned PrecompiledOp - this should be impossible!")
                }
                _ => panic!("Expected Number(3), got {:?}", result),
            }
        }

        #[test]
        fn test_special_forms_via_precompiled_ops() {
            // Special forms should work through PrecompiledOps in main eval()
            assert_eq!(eval_string("(quote foo)").unwrap(), sym("foo"));
            assert_eq!(eval_string("(if #t 1 2)").unwrap(), val(1));
            assert_eq!(eval_string("(and #t #t)").unwrap(), val(true));
            assert_eq!(eval_string("(or #f #t)").unwrap(), val(true));
        }

        #[test]
        fn test_builtin_functions_via_precompiled_ops() {
            // Builtin functions should work through PrecompiledOps (fast path)
            assert_eq!(eval_string("(+ 1 2 3)").unwrap(), val(6));
            assert_eq!(eval_string("(* 2 3 4)").unwrap(), val(24));
            assert_eq!(eval_string("(equal? 5 5)").unwrap(), val(true));
            assert_eq!(eval_string("(not #f)").unwrap(), val(true));
        }

        #[test]
        fn test_builtin_functions_via_dynamic_symbol_lookup() {
            // Builtin functions should also work when called dynamically through symbols
            // This exercises the eval_list -> symbol lookup -> BuiltinFunction path
            let mut env = create_global_env();

            // Store a reference to + in a variable, then call it
            eval(&parse("(define my-add +)").unwrap(), &mut env).unwrap();
            let result = eval(&parse("(my-add 10 20)").unwrap(), &mut env).unwrap();
            assert_eq!(result, val(30));

            // Store reference to equal? and call it
            eval(&parse("(define my-eq equal?)").unwrap(), &mut env).unwrap();
            let result = eval(&parse("(my-eq 5 5)").unwrap(), &mut env).unwrap();
            assert_eq!(result, val(true));
        }

        #[test]
        fn test_lambda_functions_via_eval_list() {
            // User-defined lambda functions should work through eval_list
            let mut env = create_global_env();

            // Define a lambda and call it immediately
            let result = eval(&parse("((lambda (x y) (+ x y)) 3 4)").unwrap(), &mut env).unwrap();
            assert_eq!(result, val(7));

            // Define a lambda, store it, and call it
            eval(
                &parse("(define add-one (lambda (x) (+ x 1)))").unwrap(),
                &mut env,
            )
            .unwrap();
            let result = eval(&parse("(add-one 42)").unwrap(), &mut env).unwrap();
            assert_eq!(result, val(43));
        }

        #[test]
        fn test_quoted_expressions_preserve_structure() {
            // quote should return the unoptimized structure, never PrecompiledOps
            let result = eval_string("(quote (+ 1 2))").unwrap();
            match result {
                Value::List(elements) => {
                    assert_eq!(elements.len(), 3);
                    assert_eq!(elements[0], sym("+"));
                    assert_eq!(elements[1], val(1));
                    assert_eq!(elements[2], val(2));
                    // Critically: this should NOT be a PrecompiledOp
                    for elem in &elements {
                        if let Value::PrecompiledOp { .. } = elem {
                            panic!(
                                "Found PrecompiledOp in quoted structure - should be impossible!"
                            );
                        }
                    }
                }
                Value::PrecompiledOp { .. } => {
                    panic!("quote returned PrecompiledOp - should be impossible!")
                }
                _ => panic!("Expected List from (quote (+ 1 2)), got {:?}", result),
            }
        }

        #[test]
        fn test_define_with_various_value_types() {
            let mut env = create_global_env();

            // Define numbers, booleans, strings
            eval(&parse("(define x 42)").unwrap(), &mut env).unwrap();
            eval(&parse("(define flag #t)").unwrap(), &mut env).unwrap();
            eval(&parse("(define name \"test\")").unwrap(), &mut env).unwrap();

            assert_eq!(eval(&parse("x").unwrap(), &mut env).unwrap(), val(42));
            assert_eq!(eval(&parse("flag").unwrap(), &mut env).unwrap(), val(true));
            assert_eq!(
                eval(&parse("name").unwrap(), &mut env).unwrap(),
                val("test")
            );

            // Define and retrieve builtin functions
            eval(&parse("(define my-plus +)").unwrap(), &mut env).unwrap();
            let result = eval(&parse("my-plus").unwrap(), &mut env).unwrap();
            match result {
                Value::BuiltinFunction { .. } => {} // Good - should be BuiltinFunction
                Value::PrecompiledOp { .. } => {
                    panic!("define stored PrecompiledOp - should be impossible!")
                }
                _ => panic!("Expected BuiltinFunction, got {:?}", result),
            }
        }

        #[test]
        fn test_dynamic_function_calls_in_operator_position() {
            let mut env = create_global_env();

            // Test that expressions in operator position are evaluated correctly
            // ((if #t + *) 2 3) should evaluate the if, get +, then apply it
            let result = eval(&parse("((if #t + *) 2 3)").unwrap(), &mut env).unwrap();
            assert_eq!(result, val(5)); // + was chosen, 2 + 3 = 5

            let result = eval(&parse("((if #f + *) 2 3)").unwrap(), &mut env).unwrap();
            assert_eq!(result, val(6)); // * was chosen, 2 * 3 = 6

            // Test lambda in operator position
            let result = eval(&parse("((lambda (x) (* x x)) 4)").unwrap(), &mut env).unwrap();
            assert_eq!(result, val(16)); // 4 * 4 = 16
        }

        #[test]
        fn test_nested_evaluation_paths() {
            // Test deeply nested expressions that exercise multiple evaluation paths
            let mut env = create_global_env();

            // Mix of PrecompiledOps, special forms, and function calls
            eval(
                &parse("(define square (lambda (x) (* x x)))").unwrap(),
                &mut env,
            )
            .unwrap();

            // This expression exercises:
            // - if (special form via PrecompiledOp)
            // - > (builtin via PrecompiledOp)
            // - square (lambda via dynamic call)
            // - + (builtin via PrecompiledOp)
            let result =
                eval(&parse("(if (> 5 3) (square (+ 2 1)) 0)").unwrap(), &mut env).unwrap();
            assert_eq!(result, val(9)); // (+ 2 1) = 3, square(3) = 9
        }

        #[test]
        fn test_error_cases_dont_leak_precompiled_ops() {
            // Even in error cases, we should never see PrecompiledOps as values

            // Test arity errors (- requires at least 1 arg, so (-) should fail)
            let result = eval_string("(-)");
            assert!(result.is_err());

            // Test type errors
            let result = eval_string("(+ 1 \"hello\")");
            assert!(result.is_err());

            // Test unbound variable
            let result = eval_string("undefined-var");
            assert!(result.is_err());

            // In all error cases, we never encounter PrecompiledOp values in eval_list
            // because they're consumed in the main eval() function
        }

        #[test]
        fn test_self_evaluating_forms() {
            // Ensure PrecompiledOp is NOT self-evaluating (confirmed by its absence from the match)
            assert_eq!(eval_string("42").unwrap(), val(42));
            assert_eq!(eval_string("#t").unwrap(), val(true));
            assert_eq!(eval_string("\"hello\"").unwrap(), val("hello"));

            // BuiltinFunction and Function are self-evaluating
            let mut env = create_global_env();
            eval(&parse("(define f +)").unwrap(), &mut env).unwrap();
            let result = eval(&parse("f").unwrap(), &mut env).unwrap();
            match result {
                Value::BuiltinFunction { .. } => {} // Self-evaluating
                _ => panic!("Expected BuiltinFunction to be self-evaluating"),
            }
        }

        #[test]
        fn test_impossible_precompiled_op_in_eval_list() {
            // This test documents that PrecompiledOp can never reach eval_list
            // as a function value, justifying the removal of that match arm

            // All these should work without ever encountering PrecompiledOp in eval_list:
            let mut env = create_global_env();

            // 1. Direct builtin calls (via PrecompiledOp in main eval)
            assert!(eval(&parse("(+ 1 2)").unwrap(), &mut env).is_ok());

            // 2. Dynamic builtin calls (via BuiltinFunction in eval_list)
            eval(&parse("(define add +)").unwrap(), &mut env).unwrap();
            assert!(eval(&parse("(add 1 2)").unwrap(), &mut env).is_ok());

            // 3. Lambda calls (via Function in eval_list)
            eval(
                &parse("(define sq (lambda (x) (* x x)))").unwrap(),
                &mut env,
            )
            .unwrap();
            assert!(eval(&parse("(sq 3)").unwrap(), &mut env).is_ok());

            // 4. Complex nested calls - still no PrecompiledOp in eval_list
            assert!(eval(&parse("((lambda (f x) (f x x)) + 5)").unwrap(), &mut env).is_ok());

            // The absence of PrecompiledOp match arm in eval_list is justified
            // because PrecompiledOps are consumed by main eval(), never produced
        }

        #[test]
        fn test_and_or_strict_boolean_validation() {
            let mut env = create_global_env();

            // Valid boolean operations
            assert_eq!(
                eval(&parse("(and #t #t)").unwrap(), &mut env).unwrap(),
                Value::Bool(true)
            );
            assert_eq!(
                eval(&parse("(and #f #t)").unwrap(), &mut env).unwrap(),
                Value::Bool(false)
            );
            assert_eq!(
                eval(&parse("(or #f #f)").unwrap(), &mut env).unwrap(),
                Value::Bool(false)
            );
            assert_eq!(
                eval(&parse("(or #t #f)").unwrap(), &mut env).unwrap(),
                Value::Bool(true)
            );

            // Invalid: obvious non-booleans should fail
            assert!(eval(&parse("(and 1 #t)").unwrap(), &mut env).is_err());
            assert!(eval(&parse("(and \"hello\" #t)").unwrap(), &mut env).is_err());
            assert!(eval(&parse("(or #t 42)").unwrap(), &mut env).is_err());
            assert!(eval(&parse("(or \"false\" #f)").unwrap(), &mut env).is_err());

            // Invalid: function calls that return non-booleans
            assert!(eval(&parse("(and (+ 1 2) #t)").unwrap(), &mut env).is_err());
            assert!(eval(&parse("(or #f (car '(hello)))").unwrap(), &mut env).is_err());

            // Edge case: short-circuiting still validates all args first
            assert!(eval(&parse("(and #f 123)").unwrap(), &mut env).is_err());
            assert!(eval(&parse("(or #t \"not-bool\")").unwrap(), &mut env).is_err());
        }

        #[test]
        fn test_if_special_form_strict() {
            let mut env = create_global_env();

            // Valid if expressions
            assert_eq!(
                eval(&parse("(if #t 42 0)").unwrap(), &mut env).unwrap(),
                Value::Number(42)
            );
            assert_eq!(
                eval(&parse("(if #f 42 0)").unwrap(), &mut env).unwrap(),
                Value::Number(0)
            );
            assert_eq!(
                eval(&parse("(if (> 5 3) \"big\" \"small\")").unwrap(), &mut env).unwrap(),
                Value::String("big".to_string())
            );

            // Invalid: non-boolean conditions
            assert!(eval(&parse("(if 1 42 0)").unwrap(), &mut env).is_err());
            assert!(eval(&parse("(if \"hello\" 42 0)").unwrap(), &mut env).is_err());
            assert!(eval(&parse("(if () 42 0)").unwrap(), &mut env).is_err());

            // Valid: complex conditions that evaluate to booleans
            assert_eq!(
                eval(&parse("(if (and #t #t) 42 0)").unwrap(), &mut env).unwrap(),
                Value::Number(42)
            );
            assert_eq!(
                eval(&parse("(if (not #f) 42 0)").unwrap(), &mut env).unwrap(),
                Value::Number(42)
            );

            // Arity errors are caught at parse time, not evaluation time
            assert!(parse("(if #t 42)").is_err()); // Too few args
            assert!(parse("(if #t 42 0 extra)").is_err()); // Too many args
            assert!(parse("(if)").is_err()); // No args
        }

        #[test]
        fn test_lambda_and_define_edge_cases() {
            let mut env = create_global_env();

            // Test lambda with various parameter patterns
            eval(&parse("(define id (lambda (x) x))").unwrap(), &mut env).unwrap();
            assert_eq!(eval(&parse("(id 42)").unwrap(), &mut env).unwrap(), val(42));

            // Test lambda with multiple parameters
            eval(
                &parse("(define add3 (lambda (a b c) (+ a b c)))").unwrap(),
                &mut env,
            )
            .unwrap();
            assert_eq!(
                eval(&parse("(add3 1 2 3)").unwrap(), &mut env).unwrap(),
                val(6)
            );

            // Test lambda with no parameters
            eval(&parse("(define const42 (lambda () 42))").unwrap(), &mut env).unwrap();
            assert_eq!(
                eval(&parse("(const42)").unwrap(), &mut env).unwrap(),
                val(42)
            );

            // Test closures capture environment
            eval(&parse("(define x 10)").unwrap(), &mut env).unwrap();
            eval(
                &parse("(define add-x (lambda (y) (+ x y)))").unwrap(),
                &mut env,
            )
            .unwrap();
            assert_eq!(
                eval(&parse("(add-x 5)").unwrap(), &mut env).unwrap(),
                val(15)
            );

            // Test nested lambdas
            eval(
                &parse("(define make-adder (lambda (n) (lambda (x) (+ n x))))").unwrap(),
                &mut env,
            )
            .unwrap();
            eval(&parse("(define add5 (make-adder 5))").unwrap(), &mut env).unwrap();
            assert_eq!(eval(&parse("(add5 3)").unwrap(), &mut env).unwrap(), val(8));

            // Test lambda arity checking
            assert!(eval(&parse("(id)").unwrap(), &mut env).is_err()); // Too few args
            assert!(eval(&parse("(id 1 2)").unwrap(), &mut env).is_err()); // Too many args

            // Test define with function values
            eval(&parse("(define plus +)").unwrap(), &mut env).unwrap();
            assert_eq!(
                eval(&parse("(plus 2 3)").unwrap(), &mut env).unwrap(),
                val(5)
            );

            // Test redefining variables
            eval(&parse("(define y 100)").unwrap(), &mut env).unwrap();
            assert_eq!(eval(&parse("y").unwrap(), &mut env).unwrap(), val(100));
            eval(&parse("(define y 200)").unwrap(), &mut env).unwrap();
            assert_eq!(eval(&parse("y").unwrap(), &mut env).unwrap(), val(200));
        }

        #[test]
        fn test_quote_and_symbolic_data() {
            let mut env = create_global_env();

            // Test basic quoting
            assert_eq!(
                eval(&parse("(quote hello)").unwrap(), &mut env).unwrap(),
                sym("hello")
            );
            assert_eq!(
                eval(&parse("'hello").unwrap(), &mut env).unwrap(),
                sym("hello")
            );

            // Test quoted lists
            assert_eq!(
                eval(&parse("'(1 2 3)").unwrap(), &mut env).unwrap(),
                val([val(1), val(2), val(3)])
            );

            // Test nested quoted structures
            assert_eq!(
                eval(&parse("'(+ 1 2)").unwrap(), &mut env).unwrap(),
                val([sym("+"), val(1), val(2)])
            );

            // Test that quoted expressions don't evaluate
            assert_eq!(
                eval(&parse("'(undefined-function 123)").unwrap(), &mut env).unwrap(),
                val([sym("undefined-function"), val(123)])
            );

            // Test quote with various data types
            assert_eq!(eval(&parse("'42").unwrap(), &mut env).unwrap(), val(42));
            assert_eq!(eval(&parse("'#t").unwrap(), &mut env).unwrap(), val(true));
            assert_eq!(
                eval(&parse("'\"string\"").unwrap(), &mut env).unwrap(),
                val("string")
            );
        }

        #[test]
        fn test_error_propagation_and_handling() {
            let mut env = create_global_env();

            // Test undefined variable errors
            assert!(eval(&parse("undefined-var").unwrap(), &mut env).is_err());

            // Test arity errors propagate through calls
            assert!(parse("(car 1 2)").is_err()); // Wrong arity for car (caught at parse time)

            // Test type errors propagate through calls
            assert!(eval(&parse("(not 42)").unwrap(), &mut env).is_err()); // Type error
            assert!(eval(&parse("(car \"not-a-list\")").unwrap(), &mut env).is_err()); // Type error

            // Test errors in nested expressions
            assert!(eval(&parse("(+ 1 (car \"not-a-list\"))").unwrap(), &mut env).is_err());
            assert!(eval(&parse("(if (not 42) 1 2)").unwrap(), &mut env).is_err());

            // Test lambda parameter errors
            assert!(eval(&parse("(lambda (x x) x)").unwrap(), &mut env).is_err()); // Duplicate params
            assert!(eval(&parse("(lambda \"not-a-list\" 42)").unwrap(), &mut env).is_err()); // Invalid params

            // Test define errors
            assert!(eval(&parse("(define 123 42)").unwrap(), &mut env).is_err()); // Invalid var name
            assert!(eval(&parse("(define \"not-symbol\" 42)").unwrap(), &mut env).is_err()); // Invalid var name
        }

        #[test]
        fn test_environment_scoping_edge_cases() {
            let mut env = create_global_env();

            // Test global vs local scope
            eval(&parse("(define x 1)").unwrap(), &mut env).unwrap();
            eval(
                &parse("(define f (lambda (x) (+ x 10)))").unwrap(),
                &mut env,
            )
            .unwrap();
            assert_eq!(eval(&parse("(f 5)").unwrap(), &mut env).unwrap(), val(15));
            assert_eq!(eval(&parse("x").unwrap(), &mut env).unwrap(), val(1)); // Global x unchanged

            // Test closure behavior with variable redefinition
            eval(&parse("(define y 100)").unwrap(), &mut env).unwrap();
            eval(&parse("(define g (lambda () y))").unwrap(), &mut env).unwrap();
            eval(&parse("(define y 200)").unwrap(), &mut env).unwrap(); // Redefine y
            // This implementation uses lexical scoping - closures see binding at definition time
            assert_eq!(eval(&parse("(g)").unwrap(), &mut env).unwrap(), val(100));

            // Test nested function definitions
            eval(
                &parse("(define outer (lambda (a) (lambda (b) (+ a b))))").unwrap(),
                &mut env,
            )
            .unwrap();
            eval(&parse("(define add10 (outer 10))").unwrap(), &mut env).unwrap();
            assert_eq!(
                eval(&parse("(add10 5)").unwrap(), &mut env).unwrap(),
                val(15)
            );
        }
    }
}
