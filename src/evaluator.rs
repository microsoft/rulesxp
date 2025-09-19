use crate::{Environment, SchemeError, Value};

/// Evaluate an S-expression in the given environment
pub fn eval(expr: &Value, env: &mut Environment) -> Result<Value, SchemeError> {
    match expr {
        // Self-evaluating forms
        Value::Number(_) | Value::String(_) | Value::Bool(_) | Value::Nil 
        | Value::BuiltinFunction(_) | Value::Function { .. } => Ok(expr.clone()),
        
        // Variable lookup
        Value::Symbol(name) => {
            env.get(name)
                .cloned()
                .ok_or_else(|| SchemeError::UnboundVariable(name.clone()))
        }
        
        // List evaluation (function application or special forms)
        Value::List(elements) => {
            if elements.is_empty() {
                return Err(SchemeError::EvalError("Cannot evaluate empty list".to_string()));
            }
            
            match &elements[0] {
                // Special forms
                Value::Symbol(name) => match name.as_str() {
                    "quote" => eval_quote(&elements[1..]),
                    "define" => eval_define(&elements[1..], env),
                    "if" => eval_if(&elements[1..], env),
                    "lambda" => eval_lambda(&elements[1..], env),
                    "and" => eval_and(&elements[1..], env),
                    "or" => eval_or(&elements[1..], env),
                    _ => eval_application(elements, env),
                },
                _ => eval_application(elements, env),
            }
        }
    }
}

/// Evaluate quote special form
fn eval_quote(args: &[Value]) -> Result<Value, SchemeError> {
    if args.len() != 1 {
        return Err(SchemeError::ArityError { expected: 1, got: args.len() });
    }
    Ok(args[0].clone())
}

/// Evaluate define special form
fn eval_define(args: &[Value], env: &mut Environment) -> Result<Value, SchemeError> {
    if args.len() != 2 {
        return Err(SchemeError::ArityError { expected: 2, got: args.len() });
    }
    
    match &args[0] {
        Value::Symbol(name) => {
            let value = eval(&args[1], env)?;
            env.define(name.clone(), value.clone());
            Ok(Value::Symbol(name.clone()))
        }
        _ => Err(SchemeError::TypeError("define requires a symbol".to_string())),
    }
}

/// Evaluate if special form
fn eval_if(args: &[Value], env: &mut Environment) -> Result<Value, SchemeError> {
    if args.len() < 2 || args.len() > 3 {
        return Err(SchemeError::ArityError { expected: 2, got: args.len() });
    }
    
    let condition = eval(&args[0], env)?;
    
    if condition.is_truthy() {
        eval(&args[1], env)
    } else if args.len() == 3 {
        eval(&args[2], env)
    } else {
        Ok(Value::Nil)
    }
}

/// Evaluate lambda special form
fn eval_lambda(args: &[Value], env: &Environment) -> Result<Value, SchemeError> {
    if args.len() != 2 {
        return Err(SchemeError::ArityError { expected: 2, got: args.len() });
    }
    
    // Extract parameter names
    let params = match &args[0] {
        Value::List(param_list) => {
            let mut params = Vec::new();
            for param in param_list {
                match param {
                    Value::Symbol(name) => params.push(name.clone()),
                    _ => return Err(SchemeError::TypeError("Lambda parameters must be symbols".to_string())),
                }
            }
            params
        }
        Value::Nil => Vec::new(),
        _ => return Err(SchemeError::TypeError("Lambda parameters must be a list".to_string())),
    };
    
    Ok(Value::Function {
        params,
        body: Box::new(args[1].clone()),
        env: env.clone(),
    })
}

/// Evaluate and special form (short-circuit evaluation)
fn eval_and(args: &[Value], env: &mut Environment) -> Result<Value, SchemeError> {
    // (and) returns #t
    if args.is_empty() {
        return Ok(Value::Bool(true));
    }
    
    // Evaluate each argument until one is falsy or we reach the end
    for (i, arg) in args.iter().enumerate() {
        let result = eval(arg, env)?;
        
        if result.is_falsy() {
            return Ok(Value::Bool(false));
        }
        
        // Return the last value if this is the final argument
        if i == args.len() - 1 {
            return Ok(result);
        }
    }
    
    // This should never be reached due to the logic above
    Ok(Value::Bool(true))
}

/// Evaluate or special form (short-circuit evaluation)
fn eval_or(args: &[Value], env: &mut Environment) -> Result<Value, SchemeError> {
    // (or) returns #f
    if args.is_empty() {
        return Ok(Value::Bool(false));
    }
    
    // Evaluate each argument until one is truthy or we reach the end
    for arg in args {
        let result = eval(arg, env)?;
        
        if result.is_truthy() {
            return Ok(result);
        }
    }
    
    // All arguments were falsy
    Ok(Value::Bool(false))
}

/// Evaluate function application
fn eval_application(elements: &[Value], env: &mut Environment) -> Result<Value, SchemeError> {
    // Evaluate the function
    let func = eval(&elements[0], env)?;
    
    // Evaluate the arguments
    let mut args = Vec::new();
    for arg in &elements[1..] {
        args.push(eval(arg, env)?);
    }
    
    // Apply the function
    apply_function(&func, &args, env)
}

/// Apply a function to its arguments
fn apply_function(func: &Value, args: &[Value], _env: &mut Environment) -> Result<Value, SchemeError> {
    match func {
        Value::BuiltinFunction(f) => f(args),
        Value::Function { params, body, env: closure_env } => {
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
            
            // Evaluate body in new environment
            eval(body, &mut new_env)
        }
        _ => Err(SchemeError::TypeError(format!("Cannot apply non-function: {}", func))),
    }
}

/// Create a global environment with built-in functions
pub fn create_global_env() -> Environment {
    let mut env = Environment::new();
    
    // Arithmetic functions
    env.define("+".to_string(), Value::BuiltinFunction(builtin_add));
    env.define("-".to_string(), Value::BuiltinFunction(builtin_sub));
    env.define("*".to_string(), Value::BuiltinFunction(builtin_mul));
    env.define("/".to_string(), Value::BuiltinFunction(builtin_div));
    
    // Comparison functions
    env.define("=".to_string(), Value::BuiltinFunction(builtin_eq));
    env.define("<".to_string(), Value::BuiltinFunction(builtin_lt));
    env.define(">".to_string(), Value::BuiltinFunction(builtin_gt));
    
    // List functions
    env.define("car".to_string(), Value::BuiltinFunction(builtin_car));
    env.define("cdr".to_string(), Value::BuiltinFunction(builtin_cdr));
    env.define("cons".to_string(), Value::BuiltinFunction(builtin_cons));
    env.define("list".to_string(), Value::BuiltinFunction(builtin_list));
    env.define("null?".to_string(), Value::BuiltinFunction(builtin_null));
    
    // Logic functions
    env.define("not".to_string(), Value::BuiltinFunction(builtin_not));
    
    env
}

// Built-in function implementations

fn builtin_add(args: &[Value]) -> Result<Value, SchemeError> {
    let mut sum = 0i64;
    for arg in args {
        match arg {
            Value::Number(n) => sum += n,
            _ => return Err(SchemeError::TypeError("+ requires numbers".to_string())),
        }
    }
    Ok(Value::Number(sum))
}

fn builtin_sub(args: &[Value]) -> Result<Value, SchemeError> {
    if args.is_empty() {
        return Err(SchemeError::ArityError { expected: 1, got: 0 });
    }
    
    match &args[0] {
        Value::Number(first) => {
            if args.len() == 1 {
                Ok(Value::Number(-first))
            } else {
                let mut result = *first;
                for arg in &args[1..] {
                    match arg {
                        Value::Number(n) => result -= n,
                        _ => return Err(SchemeError::TypeError("- requires numbers".to_string())),
                    }
                }
                Ok(Value::Number(result))
            }
        }
        _ => Err(SchemeError::TypeError("- requires numbers".to_string())),
    }
}

fn builtin_mul(args: &[Value]) -> Result<Value, SchemeError> {
    let mut product = 1i64;
    for arg in args {
        match arg {
            Value::Number(n) => product *= n,
            _ => return Err(SchemeError::TypeError("* requires numbers".to_string())),
        }
    }
    Ok(Value::Number(product))
}

fn builtin_div(args: &[Value]) -> Result<Value, SchemeError> {
    if args.is_empty() {
        return Err(SchemeError::ArityError { expected: 1, got: 0 });
    }
    
    match &args[0] {
        Value::Number(first) => {
            if args.len() == 1 {
                if *first == 0 {
                    return Err(SchemeError::EvalError("Division by zero".to_string()));
                }
                // For integer division, 1/n where n != 1 would be 0, which isn't very useful
                // Let's return an error for unary division with integers
                return Err(SchemeError::EvalError("Integer division: (/ n) not supported".to_string()));
            } else {
                let mut result = *first;
                for arg in &args[1..] {
                    match arg {
                        Value::Number(n) => {
                            if *n == 0 {
                                return Err(SchemeError::EvalError("Division by zero".to_string()));
                            }
                            result /= n; // Integer division
                        }
                        _ => return Err(SchemeError::TypeError("/ requires numbers".to_string())),
                    }
                }
                Ok(Value::Number(result))
            }
        }
        _ => Err(SchemeError::TypeError("/ requires numbers".to_string())),
    }
}

fn builtin_eq(args: &[Value]) -> Result<Value, SchemeError> {
    if args.len() != 2 {
        return Err(SchemeError::ArityError { expected: 2, got: args.len() });
    }
    
    let result = args[0] == args[1];
    Ok(Value::Bool(result))
}

fn builtin_lt(args: &[Value]) -> Result<Value, SchemeError> {
    if args.len() != 2 {
        return Err(SchemeError::ArityError { expected: 2, got: args.len() });
    }
    
    match (&args[0], &args[1]) {
        (Value::Number(a), Value::Number(b)) => Ok(Value::Bool(a < b)),
        _ => Err(SchemeError::TypeError("< requires numbers".to_string())),
    }
}

fn builtin_gt(args: &[Value]) -> Result<Value, SchemeError> {
    if args.len() != 2 {
        return Err(SchemeError::ArityError { expected: 2, got: args.len() });
    }
    
    match (&args[0], &args[1]) {
        (Value::Number(a), Value::Number(b)) => Ok(Value::Bool(a > b)),
        _ => Err(SchemeError::TypeError("> requires numbers".to_string())),
    }
}

fn builtin_car(args: &[Value]) -> Result<Value, SchemeError> {
    if args.len() != 1 {
        return Err(SchemeError::ArityError { expected: 1, got: args.len() });
    }
    
    match &args[0] {
        Value::List(list) => {
            if list.is_empty() {
                Err(SchemeError::EvalError("car of empty list".to_string()))
            } else {
                Ok(list[0].clone())
            }
        }
        _ => Err(SchemeError::TypeError("car requires a list".to_string())),
    }
}

fn builtin_cdr(args: &[Value]) -> Result<Value, SchemeError> {
    if args.len() != 1 {
        return Err(SchemeError::ArityError { expected: 1, got: args.len() });
    }
    
    match &args[0] {
        Value::List(list) => {
            if list.is_empty() {
                Err(SchemeError::EvalError("cdr of empty list".to_string()))
            } else {
                Ok(Value::List(list[1..].to_vec()))
            }
        }
        _ => Err(SchemeError::TypeError("cdr requires a list".to_string())),
    }
}

fn builtin_cons(args: &[Value]) -> Result<Value, SchemeError> {
    if args.len() != 2 {
        return Err(SchemeError::ArityError { expected: 2, got: args.len() });
    }
    
    match &args[1] {
        Value::List(list) => {
            let mut new_list = vec![args[0].clone()];
            new_list.extend_from_slice(list);
            Ok(Value::List(new_list))
        }
        Value::Nil => Ok(Value::List(vec![args[0].clone()])),
        _ => Err(SchemeError::TypeError("cons requires a list as second argument".to_string())),
    }
}

fn builtin_list(args: &[Value]) -> Result<Value, SchemeError> {
    Ok(Value::List(args.to_vec()))
}

fn builtin_null(args: &[Value]) -> Result<Value, SchemeError> {
    if args.len() != 1 {
        return Err(SchemeError::ArityError { expected: 1, got: args.len() });
    }
    
    let is_null = match &args[0] {
        Value::Nil => true,
        Value::List(list) => list.is_empty(),
        _ => false,
    };
    
    Ok(Value::Bool(is_null))
}

fn builtin_not(args: &[Value]) -> Result<Value, SchemeError> {
    if args.len() != 1 {
        return Err(SchemeError::ArityError { expected: 1, got: args.len() });
    }
    
    Ok(Value::Bool(args[0].is_falsy()))
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
        assert_eq!(eval_string("\"hello\"").unwrap(), Value::String("hello".to_string()));
    }

    #[test]
    fn test_arithmetic() {
        assert_eq!(eval_string("(+ 1 2 3)").unwrap(), Value::Number(6));
        assert_eq!(eval_string("(- 10 3 2)").unwrap(), Value::Number(5));
        assert_eq!(eval_string("(* 2 3 4)").unwrap(), Value::Number(24));
        assert_eq!(eval_string("(/ 8 2)").unwrap(), Value::Number(4));
    }

    #[test]
    fn test_quote() {
        assert_eq!(eval_string("(quote foo)").unwrap(), Value::Symbol("foo".to_string()));
        assert_eq!(eval_string("(quote (1 2 3))").unwrap(), 
                   Value::List(vec![Value::Number(1), Value::Number(2), Value::Number(3)]));
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
        assert_eq!(eval_string("(if #t 1 2)").unwrap(), Value::Number(1));
        assert_eq!(eval_string("(if #f 1 2)").unwrap(), Value::Number(2));
        assert_eq!(eval_string("(if #t 1)").unwrap(), Value::Number(1));
        assert_eq!(eval_string("(if #f 1)").unwrap(), Value::Nil);
    }

    #[test]
    fn test_list_operations() {
        assert_eq!(eval_string("(car (list 1 2 3))").unwrap(), Value::Number(1));
        assert_eq!(eval_string("(cdr (list 1 2 3))").unwrap(), 
                   Value::List(vec![Value::Number(2), Value::Number(3)]));
        assert_eq!(eval_string("(cons 1 (list 2 3))").unwrap(),
                   Value::List(vec![Value::Number(1), Value::Number(2), Value::Number(3)]));
    }

    #[test]
    fn test_logic_operators() {
        // Test 'and' operator
        assert_eq!(eval_string("(and)").unwrap(), Value::Bool(true));
        assert_eq!(eval_string("(and #t)").unwrap(), Value::Bool(true));
        assert_eq!(eval_string("(and #f)").unwrap(), Value::Bool(false));
        assert_eq!(eval_string("(and #t #t)").unwrap(), Value::Bool(true));
        assert_eq!(eval_string("(and #t #f)").unwrap(), Value::Bool(false));
        assert_eq!(eval_string("(and #f #t)").unwrap(), Value::Bool(false));
        assert_eq!(eval_string("(and 1 2 3)").unwrap(), Value::Number(3)); // returns last value
        assert_eq!(eval_string("(and 1 #f 3)").unwrap(), Value::Bool(false)); // short-circuit
        
        // Test 'or' operator
        assert_eq!(eval_string("(or)").unwrap(), Value::Bool(false));
        assert_eq!(eval_string("(or #t)").unwrap(), Value::Bool(true));
        assert_eq!(eval_string("(or #f)").unwrap(), Value::Bool(false));
        assert_eq!(eval_string("(or #t #f)").unwrap(), Value::Bool(true));
        assert_eq!(eval_string("(or #f #t)").unwrap(), Value::Bool(true));
        assert_eq!(eval_string("(or #f #f)").unwrap(), Value::Bool(false));
        assert_eq!(eval_string("(or #f 2 3)").unwrap(), Value::Number(2)); // returns first truthy value
        assert_eq!(eval_string("(or 1 2 3)").unwrap(), Value::Number(1)); // short-circuit
        
        // Test 'not' operator
        assert_eq!(eval_string("(not #t)").unwrap(), Value::Bool(false));
        assert_eq!(eval_string("(not #f)").unwrap(), Value::Bool(true));
        assert_eq!(eval_string("(not ())").unwrap(), Value::Bool(true)); // nil is falsy
        assert_eq!(eval_string("(not 0)").unwrap(), Value::Bool(false)); // 0 is truthy
        assert_eq!(eval_string("(not 42)").unwrap(), Value::Bool(false));
        assert_eq!(eval_string("(not \"hello\")").unwrap(), Value::Bool(false));
        
        // Test complex combinations
        assert_eq!(eval_string("(and (or #f #t) (not #f))").unwrap(), Value::Bool(true));
        assert_eq!(eval_string("(or (and #f #t) (not #f))").unwrap(), Value::Bool(true));
        assert_eq!(eval_string("(not (and #t #f))").unwrap(), Value::Bool(true));
    }
}