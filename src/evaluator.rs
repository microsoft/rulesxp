use crate::ast::Value;
use crate::SchemeError;
use crate::builtinops::{
    find_builtin_op_by_scheme_id, BUILTIN_OPS,
};
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
        | Value::BuiltinFunction(_)
        | Value::Function { .. } => Ok(expr.clone()),

        // Variable lookup
        Value::Symbol(name) => env
            .get(name)
            .cloned()
            .ok_or_else(|| SchemeError::UnboundVariable(name.clone())),

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

/// Evaluate a list expression (function application or special forms)
fn eval_list(elements: &[Value], env: &mut Environment) -> Result<Value, SchemeError> {
    match elements {
        [] => Err(SchemeError::EvalError(
            "Cannot evaluate empty list".to_string(),
        )),

        // Check if first element is a symbol that might be a builtin operation
        [Value::Symbol(name), args @ ..] => {
            if let Some(builtin_op) = find_builtin_op_by_scheme_id(name) {
                match &builtin_op.op_kind {
                    crate::builtinops::OpKind::SpecialForm(special_form) => {
                        // Call the special form function directly
                        special_form(args, env)
                    }
                    crate::builtinops::OpKind::Function(builtin_func) => {
                        // Evaluate arguments and call the builtin function directly
                        let evaluated_args = eval_args(args, env)?;
                        builtin_func(&evaluated_args)
                    }
                }
            } else {
                // Not a builtin, treat as normal function application
                eval_application(elements, env)
            }
        },
        _ => eval_application(elements, env),
    }
}

/// Evaluate quote special form
pub fn eval_quote(args: &[Value], _env: &mut Environment) -> Result<Value, SchemeError> {
    match args {
        [expr] => Ok(expr.clone()),
        _ => Err(SchemeError::ArityError {
            expected: 1,
            got: args.len(),
        }),
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
        _ => Err(SchemeError::ArityError {
            expected: 2,
            got: args.len(),
        }),
    }
}

/// Evaluate if special form
pub fn eval_if(args: &[Value], env: &mut Environment) -> Result<Value, SchemeError> {
    match args {
        [condition_expr, then_expr] => {
            let condition = eval(condition_expr, env)?;
            match condition {
                Value::Bool(true) => eval(then_expr, env),
                Value::Bool(false) => Ok(Value::List(vec![])), // Return nil when no else clause
                _ => Err(SchemeError::TypeError(
                    "if condition must be a boolean".to_string(),
                )),
            }
        }
        [condition_expr, then_expr, else_expr] => {
            let condition = eval(condition_expr, env)?;
            match condition {
                Value::Bool(true) => eval(then_expr, env),
                Value::Bool(false) => eval(else_expr, env),
                _ => Err(SchemeError::TypeError(
                    "if condition must be a boolean".to_string(),
                )),
            }
        }
        _ => Err(SchemeError::ArityError {
            expected: 2,
            got: args.len(),
        }),
    }
}

/// Evaluate lambda special form
pub fn eval_lambda(args: &[Value], env: &mut Environment) -> Result<Value, SchemeError> {
    match args {
        [Value::List(param_list), body] => {
            let mut params = Vec::new();
            for param in param_list {
                match param {
                    Value::Symbol(name) => params.push(name.clone()),
                    _ => {
                        return Err(SchemeError::TypeError(
                            "Lambda parameters must be symbols".to_string(),
                        ));
                    }
                }
            }
            Ok(Value::Function {
                params,
                body: Box::new(body.clone()),
                env: env.clone(),
            })
        }
        [_, _] => Err(SchemeError::TypeError(
            "Lambda parameters must be a list".to_string(),
        )),
        _ => Err(SchemeError::ArityError {
            expected: 2,
            got: args.len(),
        }),
    }
}

/// Evaluate and special form (strict boolean evaluation)
pub fn eval_and(args: &[Value], env: &mut Environment) -> Result<Value, SchemeError> {
    // (and) returns #t
    if args.is_empty() {
        return Ok(Value::Bool(true));
    }

    // Evaluate each argument and require it to be a boolean
    for arg in args.iter() {
        let result = eval(arg, env)?;

        match result {
            Value::Bool(false) => return Ok(Value::Bool(false)),
            Value::Bool(true) => continue,
            _ => {
                return Err(SchemeError::TypeError(
                    "and requires boolean arguments".to_string(),
                ));
            }
        }
    }

    // All arguments were true
    Ok(Value::Bool(true))
}

/// Evaluate or special form (strict boolean evaluation)
pub fn eval_or(args: &[Value], env: &mut Environment) -> Result<Value, SchemeError> {
    // (or) returns #f
    if args.is_empty() {
        return Ok(Value::Bool(false));
    }

    // Evaluate each argument and require it to be a boolean
    for arg in args {
        let result = eval(arg, env)?;

        match result {
            Value::Bool(true) => return Ok(Value::Bool(true)),
            Value::Bool(false) => continue,
            _ => {
                return Err(SchemeError::TypeError(
                    "or requires boolean arguments".to_string(),
                ));
            }
        }
    }

    // All arguments were false
    Ok(Value::Bool(false))
}

/// Evaluate function application
fn eval_application(elements: &[Value], env: &mut Environment) -> Result<Value, SchemeError> {
    match elements {
        [] => Err(SchemeError::EvalError(
            "Cannot apply empty list".to_string(),
        )),
        [func_expr, arg_exprs @ ..] => {
            // Evaluate the function
            let func = eval(func_expr, env)?;

            // Evaluate the arguments using helper
            let args = eval_args(arg_exprs, env)?;

            // Apply the function
            apply_function(&func, &args, env)
        }
    }
}

/// Apply a function to its arguments
fn apply_function(
    func: &Value,
    args: &[Value],
    _env: &mut Environment,
) -> Result<Value, SchemeError> {
    match func {
        Value::BuiltinFunction(f) => f(args),
        Value::Function {
            params,
            body,
            env: closure_env,
        } => {
            if params.len() != args.len() {
                return Err(SchemeError::ArityError {
                    expected: params.len(),
                    got: args.len(),
                });
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

/// Create a global environment with built-in functions
pub fn create_global_env() -> Environment {
    let mut env = Environment::new();

    // Add all regular functions from the registry
    for (&scheme_id, builtin_op) in &BUILTIN_OPS {
        if let crate::builtinops::OpKind::Function(func) = &builtin_op.op_kind {
            env.define(scheme_id.to_string(), Value::BuiltinFunction(*func));
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
        // Test if with boolean conditions
        assert_eq!(eval_string("(if #t 1 2)").unwrap(), Value::Number(1));
        assert_eq!(eval_string("(if #f 1 2)").unwrap(), Value::Number(2));
        assert_eq!(eval_string("(if #t 1)").unwrap(), Value::Number(1));
        assert_eq!(eval_string("(if #f 1)").unwrap(), Value::List(vec![])); // Empty list (nil)

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
        assert_eq!(eval_string("(and)").unwrap(), Value::Bool(true));
        assert_eq!(eval_string("(and #t)").unwrap(), Value::Bool(true));
        assert_eq!(eval_string("(and #f)").unwrap(), Value::Bool(false));
        assert_eq!(eval_string("(and #t #t)").unwrap(), Value::Bool(true));
        assert_eq!(eval_string("(and #t #f)").unwrap(), Value::Bool(false));
        assert_eq!(eval_string("(and #f #t)").unwrap(), Value::Bool(false));

        // Test that 'and' rejects non-boolean arguments
        assert!(eval_string("(and 1 2 3)").is_err()); // should error with non-booleans
        assert!(eval_string("(and 1 #f 3)").is_err()); // should error with non-booleans

        // Test 'or' operator - now requires boolean arguments
        assert_eq!(eval_string("(or)").unwrap(), Value::Bool(false));
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
}
