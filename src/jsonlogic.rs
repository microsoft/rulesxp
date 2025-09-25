use crate::SchemeError;
use crate::ast::Value;
use crate::builtinops::{Arity, BuiltinOp, find_jsonlogic_op, find_scheme_op};
use serde_json;

/// Parse JSONLogic expression into AST value for evaluation
pub fn parse_jsonlogic(input: &str) -> Result<Value, SchemeError> {
    let json_value: serde_json::Value = serde_json::from_str(input)
        .map_err(|e| SchemeError::ParseError(format!("Invalid JSON: {}", e)))?;

    compile_json_to_ast(json_value)
}

/// Compile a serde_json::Value to AST value
fn compile_json_to_ast(json: serde_json::Value) -> Result<Value, SchemeError> {
    match json {
        // Primitives
        serde_json::Value::Null => Err(SchemeError::ParseError(
            "null values are not supported in this JSONLogic implementation".to_string(),
        )),
        serde_json::Value::Bool(b) => Ok(Value::Bool(b)),
        serde_json::Value::Number(n) => {
            if let Some(i) = n.as_i64() {
                Ok(Value::Number(i))
            } else {
                Err(SchemeError::ParseError(format!(
                    "Number too large or not integer: {}",
                    n
                )))
            }
        }
        serde_json::Value::String(s) => Ok(Value::String(s)),
        serde_json::Value::Array(arr) => {
            let converted: Vec<Value> = arr
                .into_iter()
                .map(compile_json_to_ast)
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Value::List(converted))
        }
        serde_json::Value::Object(obj) => {
            if obj.len() != 1 {
                return Err(SchemeError::ParseError(
                    "JSONLogic operations must have exactly one operator".to_string(),
                ));
            }

            let (operator, operands) = obj.into_iter().next().unwrap();
            compile_jsonlogic_operation(&operator, operands)
        }
    }
}

/// Compile JSONLogic operations to S-expression function calls
fn compile_jsonlogic_operation(
    operator: &str,
    operands: serde_json::Value,
) -> Result<Value, SchemeError> {
    // Helper function to extract operands as a list, ignoring arity checks
    let extract_operand_list = |operands: serde_json::Value| -> Result<Vec<Value>, SchemeError> {
        let converted = compile_json_to_ast(operands)?;
        match converted {
            Value::List(list) => Ok(list),
            // If it's a single value, wrap it in a list
            single_value => Ok(vec![single_value]),
        }
    };

    // Helper function to create PrecompiledOp from a known builtin operation
    let create_precompiled_op = |builtin_op: &'static BuiltinOp, args: Vec<Value>| -> Value {
        Value::PrecompiledOp {
            op: builtin_op,
            op_id: builtin_op.scheme_id.to_string(),
            args,
        }
    };

    // Special cases that need manual handling
    match operator {
        // != needs special handling with binary arity validation, since equal? takes arbitrary arguments
        "!=" => {
            let args = extract_operand_list(operands)?;
            // Validate that we have exactly 2 arguments for != operation
            Arity::Exact(2).validate(args.len())?;

            let equal_builtin = find_jsonlogic_op("==").expect("== builtin should exist");
            let equal_op = create_precompiled_op(equal_builtin, args);

            let not_builtin = find_jsonlogic_op("!").expect("! builtin should exist");
            Ok(create_precompiled_op(not_builtin, vec![equal_op]))
        }

        // Variable access (JSONLogic specific)
        "var" => {
            // For now, convert {"var": "field"} to just the symbol 'field'
            // This will need data context support in the evaluator later
            match operands {
                serde_json::Value::String(var_name) => Ok(Value::Symbol(var_name)),
                _ => Err(SchemeError::ParseError(
                    "var operator requires string operand".to_string(),
                )),
            }
        }

        // For all other operations, look them up in the registry
        _ => {
            // Look up operation by JSONLogic id
            if let Some(builtin_op) = find_jsonlogic_op(operator) {
                let args = extract_operand_list(operands)?;

                // Validate arity using the builtin operation's definition
                builtin_op.validate_arity(args.len())?;

                Ok(create_precompiled_op(builtin_op, args))
            } else {
                // Operation not in registry - emit as regular list
                let args = extract_operand_list(operands)?;
                let mut result = vec![Value::Symbol(operator.to_string())];
                result.extend(args);
                Ok(Value::List(result))
            }
        }
    }
}

/// Convert an AST value back to JSONLogic format
pub fn ast_to_jsonlogic(value: &Value) -> Result<String, SchemeError> {
    let json_value = ast_to_json_value(value)?;
    serde_json::to_string(&json_value)
        .map_err(|e| SchemeError::EvalError(format!("Failed to serialize JSON: {}", e)))
}

/// Convert an AST value to serde_json::Value for JSONLogic output
fn ast_to_json_value(value: &Value) -> Result<serde_json::Value, SchemeError> {
    match value {
        Value::Number(n) => Ok(serde_json::Value::Number(serde_json::Number::from(*n))),
        Value::String(s) => Ok(serde_json::Value::String(s.clone())),
        Value::Bool(b) => Ok(serde_json::Value::Bool(*b)),
        Value::Symbol(s) => {
            // Convert symbols back to {"var": "symbol"} format
            Ok(serde_json::json!({"var": s}))
        }
        Value::List(list) if list.is_empty() => {
            // Empty list could be represented as empty array
            Ok(serde_json::Value::Array(vec![]))
        }
        Value::List(list) => {
            // Check if this is a function call (first element is a symbol)
            if let Some(Value::Symbol(op)) = list.first() {
                let args: Result<Vec<serde_json::Value>, SchemeError> =
                    list[1..].iter().map(ast_to_json_value).collect();
                let args = args?;

                // Convert Scheme operator names back to JSONLogic operators
                let jsonlogic_op = find_scheme_op(op)
                    .map(|builtin_op| builtin_op.jsonlogic_id)
                    .unwrap_or(op);

                // Always use array format for all operations (including zero arguments)
                Ok(serde_json::json!({jsonlogic_op: args}))
            } else {
                // Convert list elements
                let converted: Result<Vec<serde_json::Value>, SchemeError> =
                    list.iter().map(ast_to_json_value).collect();
                Ok(serde_json::Value::Array(converted?))
            }
        }
        Value::BuiltinFunction { .. } => Err(SchemeError::EvalError(
            "Cannot convert builtin function to JSONLogic".to_string(),
        )),
        Value::PrecompiledOp { op, args, .. } => {
            // Convert Scheme operator names back to JSONLogic operators
            let jsonlogic_op = op.jsonlogic_id;

            // Convert arguments
            let converted_args: Result<Vec<serde_json::Value>, SchemeError> =
                args.iter().map(ast_to_json_value).collect();
            let args = converted_args?;

            // Always use array format for all operations (including zero arguments)
            Ok(serde_json::json!({jsonlogic_op: args}))
        }
        Value::Function { .. } => Err(SchemeError::EvalError(
            "Cannot convert user function to JSONLogic".to_string(),
        )),
        Value::Unspecified => Err(SchemeError::EvalError(
            "Cannot convert unspecified value to JSONLogic".to_string(),
        )),
    }
}

#[cfg(test)]
mod tests {
    use core::panic;

    use super::*;
    use crate::evaluator::{create_global_env, eval};
    use crate::parser::parse as parse_scheme;

    #[derive(Debug)]
    enum TestResult {
        Identical(&'static str),
        IdenticalDontEvaluate(&'static str),
        SemanticallyEquivalent(&'static str),
        Error,
    }
    use TestResult::*;

    #[test]
    fn test_jsonlogic_to_scheme_equivalence() {
        // Test cases as tuples: (jsonlogic, scheme_equivalent)
        // None for scheme_equivalent means we expect an error
        let test_cases = [
            // Basic primitives
            ("true", Identical("#t")),
            ("false", Identical("#f")),
            ("42", Identical("42")),
            (r#""hello""#, Identical(r#""hello""#)),
            // Note: Array literals [1,2,3] are converted to lists (1 2 3) which would
            // try to call 1 as a function. This is a semantic mismatch between JSONLogic
            // arrays and Scheme lists that needs separate handling.

            // Arithmetic operations
            (r#"{"+": [1, 2, 3]}"#, Identical("(+ 1 2 3)")),
            (r#"{"+": []}"#, Identical("(+)")),
            (r#"{"-": [10, 3]}"#, Identical("(- 10 3)")),
            (r#"{"*": [2, 3, 4]}"#, Identical("(* 2 3 4)")),
            // Comparison operations
            (r#"{"==": [1, 2]}"#, Identical("(equal? 1 2)")),
            (r#"{">": [5, 3]}"#, Identical("(> 5 3)")),
            (r#"{"<": [2, 5]}"#, Identical("(< 2 5)")),
            (r#"{">=": [5, 5]}"#, Identical("(>= 5 5)")),
            (r#"{"<=": [3, 5]}"#, Identical("(<= 3 5)")),
            // Logical operations
            (r#"{"and": [true, false]}"#, Identical("(and #t #f)")),
            (r#"{"or": [false, false]}"#, Identical("(or #f #f)")),
            (r#"{"!": [true]}"#, Identical("(not #t)")),
            // Special != operation (expands to (not (equal? ...))) - use SemanticallyEquivalent since roundtrip differs
            (
                r#"{"!=": [1, 2]}"#,
                SemanticallyEquivalent("(not (equal? 1 2))"),
            ),
            // Conditional operations
            (
                r#"{"if": [true, "yes", "no"]}"#,
                Identical(r#"(if #t "yes" "no")"#),
            ),
            (
                r#"{"if": [false, "yes", "no"]}"#,
                Identical(r#"(if #f "yes" "no")"#),
            ),
            // Variable operations (simple symbol conversion)
            (r#"{"var": "age"}"#, IdenticalDontEvaluate("age")),
            // Nested operations
            (
                r#"{"and": [true, {">": [5, 3]}]}"#,
                Identical("(and #t (> 5 3))"),
            ),
            (
                r#"{"if": [{">": [10, 5]}, "big", "small"]}"#,
                Identical(r#"(if (> 10 5) "big" "small")"#),
            ),
            // Unknown operations should still be emitted
            (
                r#"{"unknown": [1, 2, 3]}"#,
                IdenticalDontEvaluate("(unknown 1 2 3)"),
            ),
            (
                r#"{"unknown_zero_args": []}"#,
                IdenticalDontEvaluate("(unknown_zero_args)"),
            ),
            // Error cases
            ("null", Error),                     // Null values should be rejected
            (r#"{"!=": [1]}"#, Error),           // Not equal with wrong arity should fail
            (r#"{"!=": [1, 2, 3]}"#, Error),     // Not equal with too many args should fail
            (r#"{"if": [true, "yes"]}"#, Error), // If with wrong arity should fail
            ("invalid json", Error),             // Invalid JSON should fail
            (r#"{"and": true, "or": false}"#, Error), // Multiple keys in object should fail
        ];

        run_data_driven_tests(&test_cases);
    }

    /// Helper function to test AST equivalence and roundtrip (shared by Identical and IdenticalDontEvaluate)
    fn test_ast_equivalence_and_roundtrip(
        jsonlogic: &str,
        jsonlogic_ast: &Value,
        expected_scheme: &str,
    ) {
        let scheme_ast = parse_scheme(expected_scheme).unwrap();
        assert!(jsonlogic_ast == &scheme_ast);

        // Test JSONLogic -> AST -> JSONLogic roundtrip (should always work)
        let back_to_json = ast_to_jsonlogic(jsonlogic_ast).unwrap();
        // Parse both JSON strings to compare structure rather than formatting
        let original_json: serde_json::Value = serde_json::from_str(jsonlogic).unwrap();
        let roundtrip_json: serde_json::Value = serde_json::from_str(&back_to_json).unwrap();
        assert_eq!(
            roundtrip_json, original_json,
            "Roundtrip failed: {} -> {} (expected {})",
            jsonlogic, back_to_json, jsonlogic
        );
    }

    /// Helper function to run data-driven tests
    fn run_data_driven_tests(test_cases: &[(&str, TestResult)]) {
        for (jsonlogic, expected_result) in test_cases {
            println!(
                "Testing JSONLogic: {}, expected: {:?}",
                jsonlogic, expected_result
            );

            match (parse_jsonlogic(jsonlogic), expected_result) {
                (Ok(jsonlogic_ast), Identical(expected_scheme)) => {
                    test_ast_equivalence_and_roundtrip(jsonlogic, &jsonlogic_ast, expected_scheme);
                    // Test evaluation of AST as well
                    assert!(eval(&jsonlogic_ast, &mut create_global_env()).is_ok());
                }
                (Ok(jsonlogic_ast), IdenticalDontEvaluate(expected_scheme)) => {
                    test_ast_equivalence_and_roundtrip(jsonlogic, &jsonlogic_ast, expected_scheme);
                }
                (Ok(jsonlogic_ast), SemanticallyEquivalent(expected_scheme)) => {
                    let scheme_ast = parse_scheme(expected_scheme).unwrap();
                    let jsonlogic_val = eval(&jsonlogic_ast, &mut create_global_env()).unwrap();
                    let scheme_val = eval(&scheme_ast, &mut create_global_env()).unwrap();
                    assert_eq!(jsonlogic_val, scheme_val);

                    // For semantic equivalence tests, also verify that roundtrip produces different
                    // but semantically equivalent JSONLogic (like != expanding to not+equal)
                    if let Ok(back_to_json) = ast_to_jsonlogic(&jsonlogic_ast)
                        && back_to_json != *jsonlogic
                    {
                        // Verify that the roundtrip version also evaluates to the same result
                        let roundtrip_parsed = parse_jsonlogic(&back_to_json).unwrap();
                        let roundtrip_result =
                            eval(&roundtrip_parsed, &mut create_global_env()).unwrap();
                        assert_eq!(jsonlogic_val, roundtrip_result);
                    }
                }

                (Err(_), Error) => {
                    // Expected error
                }
                (_, _) => {
                    panic!(
                        "Test failed for JSONLogic: {} Expected: {:?}",
                        jsonlogic, expected_result
                    );
                }
            }
        }
    }
}
