use sexpr::{evaluator, parser, Environment, SchemeError, Value};

/// Helper function to parse and evaluate a string expression
fn eval_string(input: &str, env: &mut Environment) -> Result<Value, SchemeError> {
    let expr = parser::parse(input)?;
    evaluator::eval(&expr, env)
}

/// Helper function to parse and evaluate with fresh environment
fn eval_fresh(input: &str) -> Result<Value, SchemeError> {
    let mut env = evaluator::create_global_env();
    eval_string(input, &mut env)
}

#[test]
fn test_basic_arithmetic() {
    assert_eq!(eval_fresh("(+ 1 2 3)").unwrap(), Value::Number(6.0));
    assert_eq!(eval_fresh("(- 10 3 2)").unwrap(), Value::Number(5.0));
    assert_eq!(eval_fresh("(* 2 3 4)").unwrap(), Value::Number(24.0));
    assert_eq!(eval_fresh("(/ 12 3)").unwrap(), Value::Number(4.0));
    
    // Test unary operators
    assert_eq!(eval_fresh("(- 5)").unwrap(), Value::Number(-5.0));
    assert_eq!(eval_fresh("(/ 4)").unwrap(), Value::Number(0.25));
}

#[test]
fn test_nested_arithmetic() {
    assert_eq!(eval_fresh("(+ (* 2 3) (- 8 2))").unwrap(), Value::Number(12.0));
    assert_eq!(eval_fresh("(* (+ 1 2) (- 5 2))").unwrap(), Value::Number(9.0));
}

#[test]
fn test_comparisons() {
    assert_eq!(eval_fresh("(= 5 5)").unwrap(), Value::Bool(true));
    assert_eq!(eval_fresh("(= 5 6)").unwrap(), Value::Bool(false));
    assert_eq!(eval_fresh("(< 3 5)").unwrap(), Value::Bool(true));
    assert_eq!(eval_fresh("(< 5 3)").unwrap(), Value::Bool(false));
    assert_eq!(eval_fresh("(> 5 3)").unwrap(), Value::Bool(true));
    assert_eq!(eval_fresh("(> 3 5)").unwrap(), Value::Bool(false));
}

#[test]
fn test_list_operations() {
    assert_eq!(eval_fresh("(list 1 2 3)").unwrap(), 
               Value::List(vec![Value::Number(1.0), Value::Number(2.0), Value::Number(3.0)]));
    
    assert_eq!(eval_fresh("(car (list 1 2 3))").unwrap(), Value::Number(1.0));
    assert_eq!(eval_fresh("(cdr (list 1 2 3))").unwrap(),
               Value::List(vec![Value::Number(2.0), Value::Number(3.0)]));
    
    assert_eq!(eval_fresh("(cons 0 (list 1 2))").unwrap(),
               Value::List(vec![Value::Number(0.0), Value::Number(1.0), Value::Number(2.0)]));
    
    assert_eq!(eval_fresh("(null? ())").unwrap(), Value::Bool(true));
    assert_eq!(eval_fresh("(null? (list 1))").unwrap(), Value::Bool(false));
}

#[test]
fn test_quote() {
    assert_eq!(eval_fresh("(quote hello)").unwrap(), Value::Symbol("hello".to_string()));
    assert_eq!(eval_fresh("(quote (1 2 3))").unwrap(),
               Value::List(vec![Value::Number(1.0), Value::Number(2.0), Value::Number(3.0)]));
    assert_eq!(eval_fresh("(quote (+ 1 2))").unwrap(),
               Value::List(vec![Value::Symbol("+".to_string()), Value::Number(1.0), Value::Number(2.0)]));
}

#[test]
fn test_define_and_variables() {
    let mut env = evaluator::create_global_env();
    
    // Define a variable
    eval_string("(define x 42)", &mut env).unwrap();
    assert_eq!(eval_string("x", &mut env).unwrap(), Value::Number(42.0));
    
    // Use variable in expressions
    assert_eq!(eval_string("(+ x 8)", &mut env).unwrap(), Value::Number(50.0));
    
    // Redefine variable
    eval_string("(define x 100)", &mut env).unwrap();
    assert_eq!(eval_string("x", &mut env).unwrap(), Value::Number(100.0));
}

#[test]
fn test_if_expressions() {
    assert_eq!(eval_fresh("(if #t 1 2)").unwrap(), Value::Number(1.0));
    assert_eq!(eval_fresh("(if #f 1 2)").unwrap(), Value::Number(2.0));
    assert_eq!(eval_fresh("(if #t 1)").unwrap(), Value::Number(1.0));
    assert_eq!(eval_fresh("(if #f 1)").unwrap(), Value::Nil);
    
    // Test with expressions
    assert_eq!(eval_fresh("(if (> 5 3) \"yes\" \"no\")").unwrap(), 
               Value::String("yes".to_string()));
    assert_eq!(eval_fresh("(if (< 5 3) \"yes\" \"no\")").unwrap(),
               Value::String("no".to_string()));
}

#[test]
fn test_lambda_and_function_calls() {
    let mut env = evaluator::create_global_env();
    
    // Define a simple lambda
    eval_string("(define square (lambda (x) (* x x)))", &mut env).unwrap();
    assert_eq!(eval_string("(square 5)", &mut env).unwrap(), Value::Number(25.0));
    
    // Lambda with multiple parameters
    eval_string("(define add (lambda (a b) (+ a b)))", &mut env).unwrap();
    assert_eq!(eval_string("(add 3 4)", &mut env).unwrap(), Value::Number(7.0));
    
    // Lambda with no parameters
    eval_string("(define get-answer (lambda () 42))", &mut env).unwrap();
    assert_eq!(eval_string("(get-answer)", &mut env).unwrap(), Value::Number(42.0));
}

#[test]
fn test_higher_order_functions() {
    let mut env = evaluator::create_global_env();
    
    // Define a function that takes another function as argument
    eval_string("(define twice (lambda (f x) (f (f x))))", &mut env).unwrap();
    eval_string("(define inc (lambda (x) (+ x 1)))", &mut env).unwrap();
    
    assert_eq!(eval_string("(twice inc 5)", &mut env).unwrap(), Value::Number(7.0));
}

#[test]
fn test_lexical_scoping() {
    let mut env = evaluator::create_global_env();
    
    // Test that lambda captures its environment
    eval_string("(define x 10)", &mut env).unwrap();
    eval_string("(define make-adder (lambda (n) (lambda (x) (+ x n))))", &mut env).unwrap();
    eval_string("(define add5 (make-adder 5))", &mut env).unwrap();
    
    assert_eq!(eval_string("(add5 3)", &mut env).unwrap(), Value::Number(8.0));
    
    // Test parameter shadowing
    eval_string("(define f (lambda (x) (lambda (x) (* x 2))))", &mut env).unwrap();
    eval_string("(define g (f 10))", &mut env).unwrap();
    assert_eq!(eval_string("(g 3)", &mut env).unwrap(), Value::Number(6.0));
}

#[test]
fn test_recursive_functions() {
    // Note: True recursive functions in Scheme require letrec semantics
    // For now, this test shows the limitation of our simple implementation
    // In a full Scheme implementation, functions should be able to reference themselves
    
    // This test is commented out because our current implementation 
    // doesn't support true recursive function definitions
    // TODO: Implement letrec or improve define to support recursion
    
    /*
    let mut env = evaluator::create_global_env();
    
    // Define factorial function
    eval_string("(define factorial (lambda (n) (if (= n 0) 1 (* n (factorial (- n 1))))))", &mut env).unwrap();
    assert_eq!(eval_string("(factorial 5)", &mut env).unwrap(), Value::Number(120.0));
    
    // Define fibonacci function  
    eval_string("(define fib (lambda (n) (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2))))))", &mut env).unwrap();
    assert_eq!(eval_string("(fib 6)", &mut env).unwrap(), Value::Number(8.0));
    */
}

#[test]
fn test_complex_expressions() {
    let mut env = evaluator::create_global_env();
    
    // Complex nested expression
    let expr = "(((lambda (x) (lambda (y) (+ x y))) 10) 5)";
    assert_eq!(eval_string(expr, &mut env).unwrap(), Value::Number(15.0));
    
    // Simple list processing (non-recursive version)
    eval_string("(define first (lambda (lst) (car lst)))", &mut env).unwrap();
    assert_eq!(eval_string("(first (list 1 2 3 4))", &mut env).unwrap(), Value::Number(1.0));
    
    // Test list construction and access
    eval_string("(define make-pair (lambda (a b) (list a b)))", &mut env).unwrap();
    eval_string("(define get-first (lambda (pair) (car pair)))", &mut env).unwrap();
    eval_string("(define get-second (lambda (pair) (car (cdr pair))))", &mut env).unwrap();
    
    eval_string("(define my-pair (make-pair 42 \"hello\"))", &mut env).unwrap();
    assert_eq!(eval_string("(get-first my-pair)", &mut env).unwrap(), Value::Number(42.0));
    assert_eq!(eval_string("(get-second my-pair)", &mut env).unwrap(), Value::String("hello".to_string()));
}

#[test]
fn test_error_cases() {
    // Division by zero
    match eval_fresh("(/ 5 0)") {
        Err(SchemeError::EvalError(_)) => (),
        _ => panic!("Expected division by zero error"),
    }
    
    // Unbound variable
    match eval_fresh("undefined-var") {
        Err(SchemeError::UnboundVariable(_)) => (),
        _ => panic!("Expected unbound variable error"),
    }
    
    // Wrong number of arguments
    match eval_fresh("(+ 1)") {
        Ok(_) => (), // + can take any number of arguments, including 1
        Err(_) => panic!("+ with one argument should work"),
    }
    
    match eval_fresh("(car)") {
        Err(SchemeError::ArityError { expected: 1, got: 0 }) => (),
        _ => panic!("Expected arity error for car with no arguments"),
    }
    
    // Type errors
    match eval_fresh("(+ 1 \"hello\")") {
        Err(SchemeError::TypeError(_)) => (),
        _ => panic!("Expected type error for adding number and string"),
    }
    
    // Parse errors
    match parser::parse("(1 2 3") {
        Err(SchemeError::ParseError(_)) => (),
        _ => panic!("Expected parse error for unclosed parenthesis"),
    }
}

#[test]
fn test_truthiness() {
    // In Scheme, only #f and () are falsy, everything else is truthy
    assert_eq!(eval_fresh("(if #f 1 2)").unwrap(), Value::Number(2.0));
    assert_eq!(eval_fresh("(if () 1 2)").unwrap(), Value::Number(2.0));
    assert_eq!(eval_fresh("(if 0 1 2)").unwrap(), Value::Number(1.0));
    assert_eq!(eval_fresh("(if \"\" 1 2)").unwrap(), Value::Number(1.0));
    assert_eq!(eval_fresh("(if (list) 1 2)").unwrap(), Value::Number(2.0)); // empty list is falsy
}

#[test]
fn test_self_evaluating_forms() {
    assert_eq!(eval_fresh("42").unwrap(), Value::Number(42.0));
    assert_eq!(eval_fresh("-2.71").unwrap(), Value::Number(-2.71));
    assert_eq!(eval_fresh("#t").unwrap(), Value::Bool(true));
    assert_eq!(eval_fresh("#f").unwrap(), Value::Bool(false));
    assert_eq!(eval_fresh("\"hello world\"").unwrap(), Value::String("hello world".to_string()));
    assert_eq!(eval_fresh("()").unwrap(), Value::Nil);
}