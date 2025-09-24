use crate::SchemeError;
use crate::ast::Value;
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
        | Value::Function { .. } => Ok(expr.clone()),

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
            Ok(Value::Symbol(name.clone()))
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

/// Evaluate and special form (strict boolean evaluation)
pub fn eval_and(args: &[Value], env: &mut Environment) -> Result<Value, SchemeError> {
    // SCHEME-STRICT: Require at least 1 argument (Scheme R7RS allows 0 args, returns #t)
    if args.is_empty() {
        return Err(SchemeError::arity_error(1, 0));
    }

    // Evaluate each argument and require it to be a boolean
    for arg in args.iter() {
        let result = eval(arg, env)?;

        match result {
            Value::Bool(false) => return Ok(Value::Bool(false)),
            Value::Bool(true) => continue,
            _ => {
                return Err(SchemeError::TypeError(
                    "SCHEME-JSONLOGIC-STRICT: and requires boolean arguments".to_string(),
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

    // Evaluate each argument and require it to be a boolean
    for arg in args {
        let result = eval(arg, env)?;

        match result {
            Value::Bool(true) => return Ok(Value::Bool(true)),
            Value::Bool(false) => continue,
            _ => {
                return Err(SchemeError::TypeError(
                    "SCHEME-JSONLOGIC-STRICT: or requires boolean arguments".to_string(),
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

    #[test]
    fn test_self_evaluating() {
        assert_eq!(eval_string("42").unwrap(), Value::Number(42));
        assert_eq!(eval_string("#t").unwrap(), Value::Bool(true));
        assert_eq!(
            eval_string("\"hello\"").unwrap(),
            Value::String("hello".to_string())
        );
    }

    #[test]
    fn test_arithmetic() {
        assert_eq!(eval_string("(+ 1 2 3)").unwrap(), Value::Number(6));
        assert_eq!(eval_string("(- 10 3 2)").unwrap(), Value::Number(5));
        assert_eq!(eval_string("(* 2 3 4)").unwrap(), Value::Number(24));
    }

    #[test]
    fn test_arithmetic_overflow() {
        // Test addition overflow
        let max_val = i64::MAX;
        let overflow_add = format!("(+ {} 1)", max_val);
        assert!(eval_string(&overflow_add).is_err());

        // Test subtraction overflow (negating MIN value)
        let min_val = i64::MIN;
        let overflow_neg = format!("(- {})", min_val);
        assert!(eval_string(&overflow_neg).is_err());

        // Test subtraction underflow
        let underflow_sub = format!("(- {} 1)", min_val);
        assert!(eval_string(&underflow_sub).is_err());

        // Test multiplication overflow
        let large_val = i64::MAX / 2 + 1;
        let overflow_mul = format!("(* {} 2)", large_val);
        assert!(eval_string(&overflow_mul).is_err());
    }

    #[test]
    fn test_comparisons() {
        // Test numeric = (spec-compliant)
        assert_eq!(eval_string("(= 5 5)").unwrap(), Value::Bool(true));
        assert_eq!(eval_string("(= 5 6)").unwrap(), Value::Bool(false));

        // Test that = rejects non-numbers
        assert!(eval_string("(= \"hello\" \"hello\")").is_err());
        assert!(eval_string("(= #t #t)").is_err());

        // Test general equality with equal?
        assert_eq!(eval_string("(equal? 5 5)").unwrap(), Value::Bool(true));
        assert_eq!(eval_string("(equal? 5 6)").unwrap(), Value::Bool(false));
        assert_eq!(
            eval_string("(equal? \"hello\" \"hello\")").unwrap(),
            Value::Bool(true)
        );
        assert_eq!(
            eval_string("(equal? \"hello\" \"world\")").unwrap(),
            Value::Bool(false)
        );
        assert_eq!(eval_string("(equal? #t #t)").unwrap(), Value::Bool(true));
        assert_eq!(eval_string("(equal? #t #f)").unwrap(), Value::Bool(false));

        // Test numeric comparisons
        assert_eq!(eval_string("(< 3 5)").unwrap(), Value::Bool(true));
        assert_eq!(eval_string("(< 5 3)").unwrap(), Value::Bool(false));
        assert_eq!(eval_string("(> 5 3)").unwrap(), Value::Bool(true));
        assert_eq!(eval_string("(> 3 5)").unwrap(), Value::Bool(false));
        assert_eq!(eval_string("(<= 3 5)").unwrap(), Value::Bool(true));
        assert_eq!(eval_string("(<= 5 5)").unwrap(), Value::Bool(true));
        assert_eq!(eval_string("(<= 5 3)").unwrap(), Value::Bool(false));
        assert_eq!(eval_string("(>= 5 3)").unwrap(), Value::Bool(true));
        assert_eq!(eval_string("(>= 5 5)").unwrap(), Value::Bool(true));
        assert_eq!(eval_string("(>= 3 5)").unwrap(), Value::Bool(false));
    }

    #[test]
    fn test_quote() {
        assert_eq!(
            eval_string("(quote foo)").unwrap(),
            Value::Symbol("foo".to_string())
        );
        assert_eq!(
            eval_string("(quote (1 2 3))").unwrap(),
            Value::List(vec![Value::Number(1), Value::Number(2), Value::Number(3)])
        );
    }

    #[test]
    fn test_define_and_lookup() {
        let mut env = create_global_env();
        let define_expr = parse("(define x 42)").unwrap();
        eval(&define_expr, &mut env).unwrap();

        let lookup_expr = parse("x").unwrap();
        assert_eq!(eval(&lookup_expr, &mut env).unwrap(), Value::Number(42));
    }

    #[test]
    fn test_if() {
        // Test if with boolean conditions - now requires exactly 3 arguments
        assert_eq!(eval_string("(if #t 1 2)").unwrap(), Value::Number(1));
        assert_eq!(eval_string("(if #f 1 2)").unwrap(), Value::Number(2));

        // SCHEME-JSONLOGIC-STRICT: Require exactly 3 arguments
        // (Scheme allows 2 args with undefined behavior, JSONLogic allows chaining with >3 args)
        assert!(eval_string("(if #t 1)").is_err()); // Too few arguments
        assert!(eval_string("(if #f 1)").is_err()); // Too few arguments

        // Test that if rejects non-boolean conditions
        assert!(eval_string("(if 0 1 2)").is_err()); // should error with non-boolean
        assert!(eval_string("(if 42 1 2)").is_err()); // should error with non-boolean
        assert!(eval_string("(if () 1 2)").is_err()); // should error with non-boolean
        assert!(eval_string("(if \"hello\" 1 2)").is_err()); // should error with non-boolean
    }

    #[test]
    fn test_list_operations() {
        assert_eq!(eval_string("(car (list 1 2 3))").unwrap(), Value::Number(1));
        assert_eq!(
            eval_string("(cdr (list 1 2 3))").unwrap(),
            Value::List(vec![Value::Number(2), Value::Number(3)])
        );
        assert_eq!(
            eval_string("(cons 1 (list 2 3))").unwrap(),
            Value::List(vec![Value::Number(1), Value::Number(2), Value::Number(3)])
        );
    }

    #[test]
    fn test_logic_operators() {
        // Test 'and' operator - now requires boolean arguments
        // SCHEME-STRICT: Require at least 1 argument (Scheme R7RS allows 0 args, returns #t)
        assert!(eval_string("(and)").is_err());
        assert_eq!(eval_string("(and #t)").unwrap(), Value::Bool(true));
        assert_eq!(eval_string("(and #f)").unwrap(), Value::Bool(false));
        assert_eq!(eval_string("(and #t #t)").unwrap(), Value::Bool(true));
        assert_eq!(eval_string("(and #t #f)").unwrap(), Value::Bool(false));
        assert_eq!(eval_string("(and #f #t)").unwrap(), Value::Bool(false));

        // Test that 'and' rejects non-boolean arguments
        assert!(eval_string("(and 1 2 3)").is_err()); // should error with non-booleans
        assert!(eval_string("(and 1 #f 3)").is_err()); // should error with non-booleans

        // Test 'or' operator - now requires boolean arguments
        // SCHEME-STRICT: Require at least 1 argument (Scheme R7RS allows 0 args, returns #f)
        assert!(eval_string("(or)").is_err());
        assert_eq!(eval_string("(or #t)").unwrap(), Value::Bool(true));
        assert_eq!(eval_string("(or #f)").unwrap(), Value::Bool(false));
        assert_eq!(eval_string("(or #t #f)").unwrap(), Value::Bool(true));
        assert_eq!(eval_string("(or #f #t)").unwrap(), Value::Bool(true));
        assert_eq!(eval_string("(or #f #f)").unwrap(), Value::Bool(false));

        // Test that 'or' rejects non-boolean arguments
        assert!(eval_string("(or #f 2 3)").is_err()); // should error with non-booleans
        assert!(eval_string("(or 1 2 3)").is_err()); // should error with non-booleans

        // Test 'not' operator - now requires boolean argument
        assert_eq!(eval_string("(not #t)").unwrap(), Value::Bool(false));
        assert_eq!(eval_string("(not #f)").unwrap(), Value::Bool(true));

        // Test that 'not' rejects non-boolean arguments
        assert!(eval_string("(not ())").is_err()); // should error with non-boolean
        assert!(eval_string("(not 0)").is_err()); // should error with non-boolean
        assert!(eval_string("(not 42)").is_err()); // should error with non-boolean
        assert!(eval_string("(not \"hello\")").is_err()); // should error with non-boolean

        // Test complex combinations (all with booleans)
        assert_eq!(
            eval_string("(and (or #f #t) (not #f))").unwrap(),
            Value::Bool(true)
        );
        assert_eq!(
            eval_string("(or (and #f #t) (not #f))").unwrap(),
            Value::Bool(true)
        );
        assert_eq!(eval_string("(not (and #t #f))").unwrap(), Value::Bool(true));
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
            assert_eq!(
                eval_string("(quote foo)").unwrap(),
                Value::Symbol("foo".to_string())
            );
            assert_eq!(eval_string("(if #t 1 2)").unwrap(), Value::Number(1));
            assert_eq!(eval_string("(and #t #t)").unwrap(), Value::Bool(true));
            assert_eq!(eval_string("(or #f #t)").unwrap(), Value::Bool(true));
        }

        #[test]
        fn test_builtin_functions_via_precompiled_ops() {
            // Builtin functions should work through PrecompiledOps (fast path)
            assert_eq!(eval_string("(+ 1 2 3)").unwrap(), Value::Number(6));
            assert_eq!(eval_string("(* 2 3 4)").unwrap(), Value::Number(24));
            assert_eq!(eval_string("(equal? 5 5)").unwrap(), Value::Bool(true));
            assert_eq!(eval_string("(not #f)").unwrap(), Value::Bool(true));
        }

        #[test]
        fn test_builtin_functions_via_dynamic_symbol_lookup() {
            // Builtin functions should also work when called dynamically through symbols
            // This exercises the eval_list -> symbol lookup -> BuiltinFunction path
            let mut env = create_global_env();

            // Store a reference to + in a variable, then call it
            eval(&parse("(define my-add +)").unwrap(), &mut env).unwrap();
            let result = eval(&parse("(my-add 10 20)").unwrap(), &mut env).unwrap();
            assert_eq!(result, Value::Number(30));

            // Store reference to equal? and call it
            eval(&parse("(define my-eq equal?)").unwrap(), &mut env).unwrap();
            let result = eval(&parse("(my-eq 5 5)").unwrap(), &mut env).unwrap();
            assert_eq!(result, Value::Bool(true));
        }

        #[test]
        fn test_lambda_functions_via_eval_list() {
            // User-defined lambda functions should work through eval_list
            let mut env = create_global_env();

            // Define a lambda and call it immediately
            let result = eval(&parse("((lambda (x y) (+ x y)) 3 4)").unwrap(), &mut env).unwrap();
            assert_eq!(result, Value::Number(7));

            // Define a lambda, store it, and call it
            eval(
                &parse("(define add-one (lambda (x) (+ x 1)))").unwrap(),
                &mut env,
            )
            .unwrap();
            let result = eval(&parse("(add-one 42)").unwrap(), &mut env).unwrap();
            assert_eq!(result, Value::Number(43));
        }

        #[test]
        fn test_quoted_expressions_preserve_structure() {
            // quote should return the unoptimized structure, never PrecompiledOps
            let result = eval_string("(quote (+ 1 2))").unwrap();
            match result {
                Value::List(elements) => {
                    assert_eq!(elements.len(), 3);
                    assert_eq!(elements[0], Value::Symbol("+".to_string()));
                    assert_eq!(elements[1], Value::Number(1));
                    assert_eq!(elements[2], Value::Number(2));
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

            assert_eq!(
                eval(&parse("x").unwrap(), &mut env).unwrap(),
                Value::Number(42)
            );
            assert_eq!(
                eval(&parse("flag").unwrap(), &mut env).unwrap(),
                Value::Bool(true)
            );
            assert_eq!(
                eval(&parse("name").unwrap(), &mut env).unwrap(),
                Value::String("test".to_string())
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
            assert_eq!(result, Value::Number(5)); // + was chosen, 2 + 3 = 5

            let result = eval(&parse("((if #f + *) 2 3)").unwrap(), &mut env).unwrap();
            assert_eq!(result, Value::Number(6)); // * was chosen, 2 * 3 = 6

            // Test lambda in operator position
            let result = eval(&parse("((lambda (x) (* x x)) 4)").unwrap(), &mut env).unwrap();
            assert_eq!(result, Value::Number(16)); // 4 * 4 = 16
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
            assert_eq!(result, Value::Number(9)); // (+ 2 1) = 3, square(3) = 9
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
            assert_eq!(eval_string("42").unwrap(), Value::Number(42));
            assert_eq!(eval_string("#t").unwrap(), Value::Bool(true));
            assert_eq!(
                eval_string("\"hello\"").unwrap(),
                Value::String("hello".to_string())
            );

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
    }
}
