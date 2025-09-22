use sexpr::ast::Value;
use sexpr::evaluator::{create_global_env, eval};
use sexpr::jsonlogic::parse_jsonlogic;
use sexpr::parser::parse as parse_scheme;

#[test]
fn test_jsonlogic_integration() {
    let mut env = create_global_env();

    // Test primitives
    assert_eq!(
        eval(&parse_jsonlogic("42").unwrap(), &mut env).unwrap(),
        Value::Number(42)
    );

    assert_eq!(
        eval(&parse_jsonlogic("true").unwrap(), &mut env).unwrap(),
        Value::Bool(true)
    );

    // Test logical operations
    assert_eq!(
        eval(
            &parse_jsonlogic(r#"{"and": [true, true]}"#).unwrap(),
            &mut env
        )
        .unwrap(),
        Value::Bool(true)
    );

    assert_eq!(
        eval(
            &parse_jsonlogic(r#"{"and": [true, false]}"#).unwrap(),
            &mut env
        )
        .unwrap(),
        Value::Bool(false)
    );

    assert_eq!(
        eval(
            &parse_jsonlogic(r#"{"or": [false, true]}"#).unwrap(),
            &mut env
        )
        .unwrap(),
        Value::Bool(true)
    );

    assert_eq!(
        eval(&parse_jsonlogic(r#"{"!": [false]}"#).unwrap(), &mut env).unwrap(),
        Value::Bool(true)
    );

    // Test comparisons
    assert_eq!(
        eval(&parse_jsonlogic(r#"{"==": [1, 1]}"#).unwrap(), &mut env).unwrap(),
        Value::Bool(true)
    );

    assert_eq!(
        eval(&parse_jsonlogic(r#"{">": [5, 3]}"#).unwrap(), &mut env).unwrap(),
        Value::Bool(true)
    );

    // Test arithmetic
    assert_eq!(
        eval(&parse_jsonlogic(r#"{"+": [1, 2, 3]}"#).unwrap(), &mut env).unwrap(),
        Value::Number(6)
    );

    assert_eq!(
        eval(&parse_jsonlogic(r#"{"-": [10, 3]}"#).unwrap(), &mut env).unwrap(),
        Value::Number(7)
    );
}

#[test]
fn test_jsonlogic_nested() {
    let mut env = create_global_env();

    // Test nested: {"and": [true, {">": [5, 3]}]}
    let result = eval(
        &parse_jsonlogic(r#"{"and": [true, {">": [5, 3]}]}"#).unwrap(),
        &mut env,
    )
    .unwrap();
    assert_eq!(result, Value::Bool(true));
}

#[test]
fn test_jsonlogic_vs_scheme() {
    let mut env = create_global_env();

    // Test that JSONLogic and equivalent Scheme produce same result
    let jsonlogic_result = eval(
        &parse_jsonlogic(r#"{"and": [true, {">": [5, 3]}]}"#).unwrap(),
        &mut env,
    )
    .unwrap();

    let scheme_result = eval(&parse_scheme("(and #t (> 5 3))").unwrap(), &mut env).unwrap();

    assert_eq!(jsonlogic_result, scheme_result);
}
