use sexpr::SchemeError;
use sexpr::ast::Value;
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
fn test_basic_arithmetic() {
    assert_eq!(eval_fresh("(+ 1 2 3)").unwrap(), Value::Number(6));
    assert_eq!(eval_fresh("(- 10 3 2)").unwrap(), Value::Number(5));
    assert_eq!(eval_fresh("(* 2 3 4)").unwrap(), Value::Number(24));

    // Test unary operators
    assert_eq!(eval_fresh("(- 5)").unwrap(), Value::Number(-5));
}

#[test]
fn test_nested_arithmetic() {
    assert_eq!(
        eval_fresh("(+ (* 2 3) (- 8 2))").unwrap(),
        Value::Number(12)
    );
    assert_eq!(eval_fresh("(* (+ 1 2) (- 5 2))").unwrap(), Value::Number(9));
}

#[test]
fn test_comparisons() {
    assert_eq!(eval_fresh("(= 5 5)").unwrap(), Value::Bool(true));
    assert_eq!(eval_fresh("(= 5 6)").unwrap(), Value::Bool(false));
    assert_eq!(eval_fresh("(< 3 5)").unwrap(), Value::Bool(true));
    assert_eq!(eval_fresh("(< 5 3)").unwrap(), Value::Bool(false));
    assert_eq!(eval_fresh("(> 5 3)").unwrap(), Value::Bool(true));
    assert_eq!(eval_fresh("(> 3 5)").unwrap(), Value::Bool(false));
    assert_eq!(eval_fresh("(<= 3 5)").unwrap(), Value::Bool(true));
    assert_eq!(eval_fresh("(<= 5 5)").unwrap(), Value::Bool(true));
    assert_eq!(eval_fresh("(<= 5 3)").unwrap(), Value::Bool(false));
    assert_eq!(eval_fresh("(>= 5 3)").unwrap(), Value::Bool(true));
    assert_eq!(eval_fresh("(>= 5 5)").unwrap(), Value::Bool(true));
    assert_eq!(eval_fresh("(>= 3 5)").unwrap(), Value::Bool(false));
}

#[test]
fn test_list_operations() {
    assert_eq!(
        eval_fresh("(list 1 2 3)").unwrap(),
        Value::List(vec![Value::Number(1), Value::Number(2), Value::Number(3)])
    );

    assert_eq!(eval_fresh("(car (list 1 2 3))").unwrap(), Value::Number(1));
    assert_eq!(
        eval_fresh("(cdr (list 1 2 3))").unwrap(),
        Value::List(vec![Value::Number(2), Value::Number(3)])
    );

    assert_eq!(
        eval_fresh("(cons 0 (list 1 2))").unwrap(),
        Value::List(vec![Value::Number(0), Value::Number(1), Value::Number(2)])
    );

    assert_eq!(eval_fresh("(null? '())").unwrap(), Value::Bool(true)); // Use quoted empty list
    assert_eq!(eval_fresh("(null? (list 1))").unwrap(), Value::Bool(false));
}

#[test]
fn test_quote() {
    // Test longhand (quote ...) syntax
    assert_eq!(
        eval_fresh("(quote hello)").unwrap(),
        Value::Symbol("hello".to_string())
    );
    assert_eq!(
        eval_fresh("(quote (1 2 3))").unwrap(),
        Value::List(vec![Value::Number(1), Value::Number(2), Value::Number(3)])
    );
    assert_eq!(
        eval_fresh("(quote (+ 1 2))").unwrap(),
        Value::List(vec![
            Value::Symbol("+".to_string()),
            Value::Number(1),
            Value::Number(2)
        ])
    );
    assert_eq!(eval_fresh("(quote ())").unwrap(), Value::List(vec![])); // Empty list (nil)

    // Test shorthand '... syntax
    assert_eq!(
        eval_fresh("'hello").unwrap(),
        Value::Symbol("hello".to_string())
    );
    assert_eq!(
        eval_fresh("'(1 2 3)").unwrap(),
        Value::List(vec![Value::Number(1), Value::Number(2), Value::Number(3)])
    );
    assert_eq!(
        eval_fresh("'(+ 1 2)").unwrap(),
        Value::List(vec![
            Value::Symbol("+".to_string()),
            Value::Number(1),
            Value::Number(2)
        ])
    );
    assert_eq!(eval_fresh("'()").unwrap(), Value::List(vec![])); // Empty list (nil)

    // Test that both forms are equivalent
    assert_eq!(
        eval_fresh("'hello").unwrap(),
        eval_fresh("(quote hello)").unwrap()
    );
    assert_eq!(
        eval_fresh("'(a b c)").unwrap(),
        eval_fresh("(quote (a b c))").unwrap()
    );
    assert_eq!(
        eval_fresh("'()").unwrap(),
        eval_fresh("(quote ())").unwrap()
    );

    // Test nested quotes
    assert_eq!(
        eval_fresh("'(quote x)").unwrap(),
        Value::List(vec![
            Value::Symbol("quote".to_string()),
            Value::Symbol("x".to_string())
        ])
    );
    assert_eq!(
        eval_fresh("''x").unwrap(),
        Value::List(vec![
            Value::Symbol("quote".to_string()),
            Value::Symbol("x".to_string())
        ])
    );

    // Test strict semantics: empty list is NOT self-evaluating (must be quoted)
    assert!(eval_fresh("()").is_err()); // Empty list should error when evaluated
    assert_eq!(eval_fresh("'()").unwrap(), Value::List(vec![])); // But quoted empty list works
}

#[test]
fn test_define_and_variables() {
    let mut env = evaluator::create_global_env();

    // Define a variable
    eval_string("(define x 42)", &mut env).unwrap();
    assert_eq!(eval_string("x", &mut env).unwrap(), Value::Number(42));

    // Use variable in expressions
    assert_eq!(eval_string("(+ x 8)", &mut env).unwrap(), Value::Number(50));

    // Redefine variable
    eval_string("(define x 100)", &mut env).unwrap();
    assert_eq!(eval_string("x", &mut env).unwrap(), Value::Number(100));
}

#[test]
fn test_if_expressions() {
    // Test if with boolean conditions - now requires exactly 3 arguments
    assert_eq!(eval_fresh("(if #t 1 2)").unwrap(), Value::Number(1));
    assert_eq!(eval_fresh("(if #f 1 2)").unwrap(), Value::Number(2));

    assert!(eval_fresh("(if #t 1)").is_err()); // Too few arguments
    assert!(eval_fresh("(if #f 1)").is_err()); // Too few arguments

    // Test with boolean expressions (these return booleans)
    assert_eq!(
        eval_fresh("(if (> 5 3) \"yes\" \"no\")").unwrap(),
        Value::String("yes".to_string())
    );
    assert_eq!(
        eval_fresh("(if (< 5 3) \"yes\" \"no\")").unwrap(),
        Value::String("no".to_string())
    );

    // Test that if rejects non-boolean conditions
    assert!(eval_fresh("(if 0 1 2)").is_err()); // should error with non-boolean
    assert!(eval_fresh("(if 42 1 2)").is_err()); // should error with non-boolean
    assert!(eval_fresh("(if () 1 2)").is_err()); // should error with non-boolean
    assert!(eval_fresh("(if \"hello\" 1 2)").is_err()); // should error with non-boolean
}

#[test]
fn test_lambda_and_function_calls() {
    let mut env = evaluator::create_global_env();

    // Define a simple lambda
    eval_string("(define square (lambda (x) (* x x)))", &mut env).unwrap();
    assert_eq!(
        eval_string("(square 5)", &mut env).unwrap(),
        Value::Number(25)
    );

    // Lambda with multiple parameters
    eval_string("(define add (lambda (a b) (+ a b)))", &mut env).unwrap();
    assert_eq!(
        eval_string("(add 3 4)", &mut env).unwrap(),
        Value::Number(7)
    );

    // Lambda with no parameters
    eval_string("(define get-answer (lambda () 42))", &mut env).unwrap();
    assert_eq!(
        eval_string("(get-answer)", &mut env).unwrap(),
        Value::Number(42)
    );

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

    assert_eq!(
        eval_string("(twice inc 5)", &mut env).unwrap(),
        Value::Number(7)
    );
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

    assert_eq!(eval_string("(add5 3)", &mut env).unwrap(), Value::Number(8));

    // Test parameter shadowing
    eval_string("(define f (lambda (x) (lambda (x) (* x 2))))", &mut env).unwrap();
    eval_string("(define g (f 10))", &mut env).unwrap();
    assert_eq!(eval_string("(g 3)", &mut env).unwrap(), Value::Number(6));
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
    assert_eq!(eval_string("(factorial 5)", &mut env).unwrap(), Value::Number(120));

    // Define fibonacci function
    eval_string("(define fib (lambda (n) (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2))))))", &mut env).unwrap();
    assert_eq!(eval_string("(fib 6)", &mut env).unwrap(), Value::Number(8));
    */
}

#[test]
fn test_complex_expressions() {
    let mut env = evaluator::create_global_env();

    // Complex nested expression
    let expr = "(((lambda (x) (lambda (y) (+ x y))) 10) 5)";
    assert_eq!(eval_string(expr, &mut env).unwrap(), Value::Number(15));

    // Simple list processing (non-recursive version)
    eval_string("(define first (lambda (lst) (car lst)))", &mut env).unwrap();
    assert_eq!(
        eval_string("(first (list 1 2 3 4))", &mut env).unwrap(),
        Value::Number(1)
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
        Value::Number(42)
    );
    assert_eq!(
        eval_string("(get-second my-pair)", &mut env).unwrap(),
        Value::String("hello".to_string())
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
        Err(SchemeError::ArityError { expected, got, expression }) => {
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
fn test_truthiness() {
    // Our interpreter requires strict boolean conditions for all boolean operators
    // This is stricter than standard Scheme but more predictable

    // if requires boolean conditions
    assert_eq!(eval_fresh("(if #f 1 2)").unwrap(), Value::Number(2));
    assert_eq!(eval_fresh("(if #t 1 2)").unwrap(), Value::Number(1));

    // Non-boolean if conditions should error
    assert!(matches!(
        eval_fresh("(if 0 1 2)"),
        Err(SchemeError::TypeError(_))
    ));
    assert!(matches!(
        eval_fresh("(if () 1 2)"),
        Err(SchemeError::EvalError(_))
    )); // () causes eval error in strict mode
    assert!(matches!(
        eval_fresh("(if \"\" 1 2)"),
        Err(SchemeError::TypeError(_))
    ));

    // and/or also require boolean arguments (stricter than standard Scheme)
    assert_eq!(eval_fresh("(and #f #t)").unwrap(), Value::Bool(false));
    assert_eq!(eval_fresh("(and #t #t)").unwrap(), Value::Bool(true));
    assert_eq!(eval_fresh("(or #f #t)").unwrap(), Value::Bool(true));
    assert_eq!(eval_fresh("(or #f #f)").unwrap(), Value::Bool(false));

    // Non-boolean and/or arguments should error
    assert!(matches!(
        eval_fresh("(and 0 1)"),
        Err(SchemeError::TypeError(_))
    ));
    assert!(matches!(
        eval_fresh("(or \"\" 1)"),
        Err(SchemeError::TypeError(_))
    ));
}

#[test]
fn test_self_evaluating_forms() {
    assert_eq!(eval_fresh("42").unwrap(), Value::Number(42));
    assert_eq!(eval_fresh("-271").unwrap(), Value::Number(-271));
    assert_eq!(eval_fresh("#t").unwrap(), Value::Bool(true));
    assert_eq!(eval_fresh("#f").unwrap(), Value::Bool(false));
    assert_eq!(
        eval_fresh("\"hello world\"").unwrap(),
        Value::String("hello world".to_string())
    );
    // Note: empty list () is NOT self-evaluating in strict mode - it should error when evaluated
    assert!(eval_fresh("()").is_err()); // Empty list should cause evaluation error
}

#[test]
fn test_logic_operators() {
    // Test 'and' with boolean inputs only
    // SCHEME-STRICT: Require at least 1 argument (Scheme R7RS allows 0 args, returns #t)
    assert!(eval_fresh("(and)").is_err());
    assert_eq!(eval_fresh("(and #t)").unwrap(), Value::Bool(true));
    assert_eq!(eval_fresh("(and #f)").unwrap(), Value::Bool(false));
    assert_eq!(eval_fresh("(and #t #t #t)").unwrap(), Value::Bool(true));
    assert_eq!(eval_fresh("(and #t #f #t)").unwrap(), Value::Bool(false));

    // Test that 'and' rejects non-boolean inputs
    assert!(eval_fresh("(and 1 2 3)").is_err()); // should error with non-booleans
    assert!(eval_fresh("(and 1 #f 3)").is_err()); // should error with non-booleans
    assert!(eval_fresh("(and \"hello\" 42)").is_err()); // should error with non-booleans

    // Test 'or' with boolean inputs only
    // SCHEME-STRICT: Require at least 1 argument (Scheme R7RS allows 0 args, returns #f)
    assert!(eval_fresh("(or)").is_err());
    assert_eq!(eval_fresh("(or #t)").unwrap(), Value::Bool(true));
    assert_eq!(eval_fresh("(or #f)").unwrap(), Value::Bool(false));
    assert_eq!(eval_fresh("(or #f #f #t)").unwrap(), Value::Bool(true));
    assert_eq!(eval_fresh("(or #f #f #f)").unwrap(), Value::Bool(false));

    // Test that 'or' rejects non-boolean inputs
    assert!(eval_fresh("(or #f 2 3)").is_err()); // should error with non-booleans
    assert!(eval_fresh("(or 1 2 3)").is_err()); // should error with non-booleans
    assert!(eval_fresh("(or () #f 42)").is_err()); // should error with non-booleans

    // Test 'not' with boolean inputs only
    assert_eq!(eval_fresh("(not #t)").unwrap(), Value::Bool(false));
    assert_eq!(eval_fresh("(not #f)").unwrap(), Value::Bool(true));

    // Test that 'not' rejects non-boolean inputs
    assert!(eval_fresh("(not ())").is_err()); // should error with non-boolean
    assert!(eval_fresh("(not 0)").is_err()); // should error with non-boolean
    assert!(eval_fresh("(not 42)").is_err()); // should error with non-boolean
    assert!(eval_fresh("(not \"hello\")").is_err()); // should error with non-boolean
    assert!(eval_fresh("(not (list))").is_err()); // should error with non-boolean
    assert!(eval_fresh("(not (list 1))").is_err()); // should error with non-boolean

    // Test combinations and complex expressions (all with booleans)
    assert_eq!(
        eval_fresh("(and (or #f #t) (not #f))").unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval_fresh("(or (and #f #t) (not #f))").unwrap(),
        Value::Bool(true)
    );
    assert_eq!(eval_fresh("(not (and #t #f))").unwrap(), Value::Bool(true));
    assert_eq!(
        eval_fresh("(and (> 5 3) (< 2 4))").unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval_fresh("(or (= 1 2) (= 2 2))").unwrap(),
        Value::Bool(true)
    );

    // Test short-circuit evaluation with functions that could fail
    let mut env = evaluator::create_global_env();

    // This should not attempt to evaluate undefined-var due to short-circuit
    assert_eq!(
        eval_string("(and #f undefined-var)", &mut env).unwrap(),
        Value::Bool(false)
    );
    assert_eq!(
        eval_string("(or #t undefined-var)", &mut env).unwrap(),
        Value::Bool(true)
    );

    // Test error cases
    match eval_fresh("(not)") {
        Err(SchemeError::ArityError { expected, got, expression }) => {
            assert_eq!(expected, 1);
            assert_eq!(got, 0);
            assert_eq!(expression.as_deref(), Some("(not)"));
        }
        _ => panic!("Expected arity error for not with no arguments"),
    }

    match eval_fresh("(not 1 2)") {
        Err(SchemeError::ArityError { expected, got, expression }) => {
            assert_eq!(expected, 1);
            assert_eq!(got, 2);
            assert_eq!(expression.as_deref(), Some("(not 1 2)"));
        }
        _ => panic!("Expected arity error for not with too many arguments"),
    }
}

#[test]
fn test_unified_nil_representation() {
    let mut env = evaluator::create_global_env();

    // Test that parsing () creates an empty list (unified nil representation)
    let empty_list = parser::parse("()").unwrap();
    assert_eq!(empty_list, Value::List(vec![]));
    assert!(empty_list.is_nil());
    assert_eq!(format!("{}", empty_list), "()");

    // Test strict evaluation semantics: () is NOT self-evaluating
    assert!(matches!(
        evaluator::eval(&empty_list, &mut env),
        Err(SchemeError::EvalError(_))
    ));

    // Test that quoted empty list works fine and represents nil
    let quoted_empty_result = eval_string("'()", &mut env).unwrap();
    assert_eq!(quoted_empty_result, Value::List(vec![]));
    assert!(quoted_empty_result.is_nil());
    assert_eq!(format!("{}", quoted_empty_result), "()");

    // Test quote longhand syntax
    let quote_longhand_result = eval_string("(quote ())", &mut env).unwrap();
    assert_eq!(quote_longhand_result, Value::List(vec![]));
    assert!(quote_longhand_result.is_nil());

    // Test that both quoted forms are equivalent
    assert_eq!(quoted_empty_result, quote_longhand_result);

    // Test null? predicate with unified nil
    assert_eq!(
        eval_string("(null? '())", &mut env).unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval_string("(null? (quote ()))", &mut env).unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval_string("(null? 42)", &mut env).unwrap(),
        Value::Bool(false)
    );
    assert_eq!(
        eval_string("(null? #f)", &mut env).unwrap(),
        Value::Bool(false)
    );
    assert_eq!(
        eval_string("(null? (list))", &mut env).unwrap(),
        Value::Bool(true)
    );

    // Test cons with nil
    assert_eq!(
        eval_string("(cons 1 '())", &mut env).unwrap(),
        Value::List(vec![Value::Number(1)])
    );
    assert_eq!(
        eval_string("(cons 'a (cons 'b '()))", &mut env).unwrap(),
        Value::List(vec![
            Value::Symbol("a".to_string()),
            Value::Symbol("b".to_string())
        ])
    );

    // Test nil behavior
    let if_result = eval_string("(if #f 42 '())", &mut env).unwrap();
    assert_eq!(if_result, Value::List(vec![]));
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
    assert_eq!(lambda_result, Value::Number(42));

    // Test list creation and manipulation
    assert_eq!(
        eval_string("(list)", &mut env).unwrap(),
        Value::List(vec![])
    );
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
        assert_eq!(nil_val, Value::List(vec![]));
    }
}
