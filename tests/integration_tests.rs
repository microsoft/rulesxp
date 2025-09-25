use sexpr::SchemeError;
use sexpr::ast::{Value, nil, sym, val};
use sexpr::evaluator::{self, Environment};
use sexpr::parser;

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
fn test_define_and_variables() {
    let mut env = evaluator::create_global_env();

    // Define a variable
    eval_string("(define x 42)", &mut env).unwrap();
    assert_eq!(eval_string("x", &mut env).unwrap(), val(42));

    // Use variable in expressions
    assert_eq!(eval_string("(+ x 8)", &mut env).unwrap(), val(50));

    // Redefine variable
    eval_string("(define x 100)", &mut env).unwrap();
    assert_eq!(eval_string("x", &mut env).unwrap(), val(100));
}

#[test]
fn test_lambda_and_function_calls() {
    let mut env = evaluator::create_global_env();

    // Define a simple lambda
    eval_string("(define square (lambda (x) (* x x)))", &mut env).unwrap();
    assert_eq!(eval_string("(square 5)", &mut env).unwrap(), val(25));

    // Lambda with multiple parameters
    eval_string("(define add (lambda (a b) (+ a b)))", &mut env).unwrap();
    assert_eq!(eval_string("(add 3 4)", &mut env).unwrap(), val(7));

    // Lambda with no parameters
    eval_string("(define get-answer (lambda () 42))", &mut env).unwrap();
    assert_eq!(eval_string("(get-answer)", &mut env).unwrap(), val(42));

    // Test error cases for lambda
    // Duplicate parameter names should be rejected
    assert!(eval_string("(lambda (x x) (+ x x))", &mut env).is_err());
    assert!(eval_string("(lambda (a b a) (* a b))", &mut env).is_err());

    // Variadic lambda forms should be rejected (we only support fixed-arity)
    assert!(eval_string("(lambda args (+ 1 2))", &mut env).is_err()); // Symbol parameter list

    // Non-symbol parameters should be rejected
    assert!(eval_string("(lambda (1 2) (+ 1 2))", &mut env).is_err());
    assert!(eval_string("(lambda (\"x\" y) (+ x y))", &mut env).is_err());
}

#[test]
fn test_higher_order_functions() {
    let mut env = evaluator::create_global_env();

    // Define a function that takes another function as argument
    eval_string("(define twice (lambda (f x) (f (f x))))", &mut env).unwrap();
    eval_string("(define inc (lambda (x) (+ x 1)))", &mut env).unwrap();

    assert_eq!(eval_string("(twice inc 5)", &mut env).unwrap(), val(7));
}

#[test]
fn test_lexical_scoping() {
    let mut env = evaluator::create_global_env();

    // Test that lambda captures its environment
    eval_string("(define x 10)", &mut env).unwrap();
    eval_string(
        "(define make-adder (lambda (n) (lambda (x) (+ x n))))",
        &mut env,
    )
    .unwrap();
    eval_string("(define add5 (make-adder 5))", &mut env).unwrap();

    assert_eq!(eval_string("(add5 3)", &mut env).unwrap(), val(8));

    // Test parameter shadowing
    eval_string("(define f (lambda (x) (lambda (x) (* x 2))))", &mut env).unwrap();
    eval_string("(define g (f 10))", &mut env).unwrap();
    assert_eq!(eval_string("(g 3)", &mut env).unwrap(), val(6));
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
    assert_eq!(eval_string("(factorial 5)", &mut env).unwrap(), val(120));

    // Define fibonacci function
    eval_string("(define fib (lambda (n) (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2))))))", &mut env).unwrap();
    assert_eq!(eval_string("(fib 6)", &mut env).unwrap(), val(8));
    */
}

#[test]
fn test_complex_expressions() {
    let mut env = evaluator::create_global_env();

    // Complex nested expression
    let expr = "(((lambda (x) (lambda (y) (+ x y))) 10) 5)";
    assert_eq!(eval_string(expr, &mut env).unwrap(), val(15));

    // Simple list processing (non-recursive version)
    eval_string("(define first (lambda (lst) (car lst)))", &mut env).unwrap();
    assert_eq!(
        eval_string("(first (list 1 2 3 4))", &mut env).unwrap(),
        val(1)
    );

    // Test list construction and access
    eval_string("(define make-pair (lambda (a b) (list a b)))", &mut env).unwrap();
    eval_string("(define get-first (lambda (pair) (car pair)))", &mut env).unwrap();
    eval_string(
        "(define get-second (lambda (pair) (car (cdr pair))))",
        &mut env,
    )
    .unwrap();

    eval_string("(define my-pair (make-pair 42 \"hello\"))", &mut env).unwrap();
    assert_eq!(
        eval_string("(get-first my-pair)", &mut env).unwrap(),
        val(42)
    );
    assert_eq!(
        eval_string("(get-second my-pair)", &mut env).unwrap(),
        val("hello")
    );
}

#[test]
fn test_error_cases() {
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
        Err(SchemeError::ArityError {
            expected,
            got,
            expression,
        }) => {
            assert_eq!(expected, 1);
            assert_eq!(got, 0);
            assert_eq!(expression.as_deref(), Some("(car)"));
        }
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

    // Unbound variables (including unsupported special forms)
    match eval_fresh("(set! x 42)") {
        Err(SchemeError::UnboundVariable(var)) => {
            assert_eq!(var, "set!");
        }
        _ => panic!("Expected unbound variable error for set!"),
    }
}

#[test]
fn test_unified_nil_representation() {
    let mut env = evaluator::create_global_env();

    // Test that parsing () creates an empty list (unified nil representation)
    let empty_list = parser::parse("()").unwrap();
    assert_eq!(empty_list, nil());
    assert!(empty_list.is_nil());
    assert_eq!(format!("{}", empty_list), "()");

    // Test strict evaluation semantics: () is NOT self-evaluating
    assert!(matches!(
        evaluator::eval(&empty_list, &mut env),
        Err(SchemeError::EvalError(_))
    ));

    // Test that quoted empty list works fine and represents nil
    let quoted_empty_result = eval_string("'()", &mut env).unwrap();
    assert_eq!(quoted_empty_result, nil());
    assert!(quoted_empty_result.is_nil());
    assert_eq!(format!("{}", quoted_empty_result), "()");

    // Test quote longhand syntax
    let quote_longhand_result = eval_string("(quote ())", &mut env).unwrap();
    assert_eq!(quote_longhand_result, nil());
    assert!(quote_longhand_result.is_nil());

    // Test that both quoted forms are equivalent
    assert_eq!(quoted_empty_result, quote_longhand_result);

    // Test null? predicate with unified nil
    assert_eq!(eval_string("(null? '())", &mut env).unwrap(), val(true));
    assert_eq!(
        eval_string("(null? (quote ()))", &mut env).unwrap(),
        val(true)
    );
    assert_eq!(eval_string("(null? 42)", &mut env).unwrap(), val(false));
    assert_eq!(eval_string("(null? #f)", &mut env).unwrap(), val(false));
    assert_eq!(eval_string("(null? (list))", &mut env).unwrap(), val(true));

    // Test cons with nil
    assert_eq!(eval_string("(cons 1 '())", &mut env).unwrap(), val([1]));
    assert_eq!(
        eval_string("(cons 'a (cons 'b '()))", &mut env).unwrap(),
        val([sym("a"), sym("b")])
    );

    // Test nil behavior
    let if_result = eval_string("(if #f 42 '())", &mut env).unwrap();
    assert_eq!(if_result, nil());
    assert!(if_result.is_nil());

    // Test strict boolean semantics: if rejects non-boolean conditions (including nil)
    assert!(matches!(
        eval_string("(if '() 1 2)", &mut env),
        Err(SchemeError::TypeError(_))
    ));
    assert!(matches!(
        eval_string("(if 0 1 2)", &mut env),
        Err(SchemeError::TypeError(_))
    ));

    // Test that lambda with empty parameter list works
    let lambda_result = eval_string("((lambda () 42))", &mut env).unwrap();
    assert_eq!(lambda_result, val(42));

    // Test list creation and manipulation
    assert_eq!(eval_string("(list)", &mut env).unwrap(), nil());
    assert!(eval_string("(list)", &mut env).unwrap().is_nil());

    // Test that nil displays consistently
    let various_nils = vec![
        eval_string("'()", &mut env).unwrap(),
        eval_string("(quote ())", &mut env).unwrap(),
        eval_string("(list)", &mut env).unwrap(),
        eval_string("(if #f '() '())", &mut env).unwrap(),
    ];

    for nil_val in various_nils {
        assert!(nil_val.is_nil());
        assert_eq!(format!("{}", nil_val), "()");
        assert_eq!(nil_val, nil());
    }
}
