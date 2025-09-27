use crate::SchemeError;
use crate::ast::Value;
use crate::builtinops::{Arity, BuiltinOp, find_jsonlogic_op, find_scheme_op};
use serde_json;

/// Indicates whether a JSON value should be treated as literal data or an operation context
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LiteralContext {
    /// The value is literal data and should use list constructors for arrays
    Yes,
    /// The value is in an operand/argument context and should not use list constructors
    No,
}

/// Parse JSONLogic expression into AST value for evaluation
pub fn parse_jsonlogic(input: &str) -> Result<Value, SchemeError> {
    let json_value: serde_json::Value = serde_json::from_str(input)
        .map_err(|e| SchemeError::ParseError(format!("Invalid JSON: {}", e)))?;

    compile_json_to_ast(json_value)
}

/// Compile a serde_json::Value to AST value
fn compile_json_to_ast(json: serde_json::Value) -> Result<Value, SchemeError> {
    compile_json_to_ast_with_context(json, LiteralContext::Yes)
}

fn compile_json_to_ast_with_context(
    json: serde_json::Value,
    context: LiteralContext,
) -> Result<Value, SchemeError> {
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
                .map(|v| compile_json_to_ast_with_context(v, LiteralContext::Yes))
                .collect::<Result<Vec<_>, _>>()?;
            if context == LiteralContext::Yes {
                // Use list constructor to create data structure without preventing evaluation
                // This makes ["a", "b"] become (list "a" "b") which is data, not a function call
                let list_op =
                    find_scheme_op("list").expect("list builtin operation must be available");
                Ok(Value::PrecompiledOp {
                    op: list_op,
                    op_id: "list".to_string(),
                    args: converted,
                })
            } else {
                // This is an operand list - return as plain list
                Ok(Value::List(converted))
            }
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
        match operands {
            serde_json::Value::Array(arr) => {
                // Convert each operand - arrays that appear as operands should use list constructors as data
                // (because they represent data values, not argument lists to be expanded)
                // Non-arrays are scalar arguments and should not use list constructors
                arr.into_iter()
                    .map(|v| {
                        let context = if matches!(v, serde_json::Value::Array(_)) {
                            LiteralContext::Yes
                        } else {
                            LiteralContext::No
                        };
                        compile_json_to_ast_with_context(v, context)
                    })
                    .collect::<Result<Vec<_>, _>>()
            }
            // Single operand - use list constructor if it's an array (data), don't modify scalars
            single => {
                let context = if matches!(single, serde_json::Value::Array(_)) {
                    LiteralContext::Yes
                } else {
                    LiteralContext::No
                };
                Ok(vec![compile_json_to_ast_with_context(single, context)?])
            }
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
                // Check if this unknown JSONLogic operator happens to be a known Scheme builtin
                // If so, reject it to prevent accidental access to Scheme symbols via JSONLogic
                if find_scheme_op(operator).is_some() {
                    Err(SchemeError::ParseError(format!(
                        "JSONLogic operator '{}' is not supported. Use the JSONLogic equivalent instead (e.g., use '!' instead of 'not').",
                        operator
                    )))
                } else {
                    // Operation not in registry and not a Scheme builtin - emit as regular list for custom operations
                    let args = extract_operand_list(operands)?;
                    let mut result = vec![Value::Symbol(operator.to_string())];
                    result.extend(args);
                    Ok(Value::List(result))
                }
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
            // Check if this is a list constructor call (array literal)
            if let Some(Value::Symbol(op)) = list.first() {
                if op == "list" {
                    // This is (list arg1 arg2 ...) - convert back to JSON array
                    let converted: Result<Vec<serde_json::Value>, SchemeError> =
                        list[1..].iter().map(ast_to_json_value).collect();
                    return Ok(serde_json::Value::Array(converted?));
                }
            }

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
            // Special case: list constructor operations should convert back to JSONLogic arrays
            if op.scheme_id == "list" {
                // Convert the list arguments back to a JSON array
                let converted: Result<Vec<serde_json::Value>, SchemeError> =
                    args.iter().map(ast_to_json_value).collect();
                return Ok(serde_json::Value::Array(converted?));
            }

            // Regular operations: convert Scheme operator names back to JSONLogic operators
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
        IdenticalWithEvalError(&'static str), // Parsing succeeds, test AST equivalence, but evaluation must fail
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
            // Array literals are converted to list constructor calls (list 1 2 3)
            // which preserves them as data structures rather than executable code
            (r#"[1,2,3]"#, Identical("(list 1 2 3)")),
            (r#"["a","b"]"#, Identical(r#"(list "a" "b")"#)),
            (r#"[]"#, Identical("(list)")),
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
            (r#"{"var": "age"}"#, IdenticalWithEvalError("age")),
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
                IdenticalWithEvalError("(unknown 1 2 3)"),
            ),
            (
                r#"{"unknown_zero_args": []}"#,
                IdenticalWithEvalError("(unknown_zero_args)"),
            ),
            // Error cases
            ("null", Error),                     // Null values should be rejected
            (r#"{"!=": [1]}"#, Error),           // Not equal with wrong arity should fail
            (r#"{"!=": [1, 2, 3]}"#, Error),     // Not equal with too many args should fail
            (r#"{"if": [true, "yes"]}"#, Error), // If with wrong arity should fail
            ("invalid json", Error),             // Invalid JSON should fail
            (r#"{"and": true, "or": false}"#, Error), // Multiple keys in object should fail
            // Design validation tests - operations intentionally rejected/different
            (
                r#"{"unknown_not": [true]}"#,
                IdenticalWithEvalError("(unknown_not #t)"),
            ), // Unknown operator becomes list
            (r#"{"/": [8, 2]}"#, IdenticalWithEvalError("(/ 8 2)")), // Division operator becomes unknown operation (not a Scheme builtin)
            (r#"{"car": [[1, 2, 3]]}"#, Error), // Scheme builtin 'car' should be rejected
            (r#"{"define": ["x", 42]}"#, Error), // Scheme builtin 'define' should be rejected
            (r#"{"!!": [[]]}"#, IdenticalWithEvalError("(!! (list))")), // Double negation becomes unknown operation (not a Scheme builtin)
            (r#"{"!!": ["0"]}"#, IdenticalWithEvalError("(!! \"0\")")), // Double negation becomes unknown operation
            (r#"{"!!": [0]}"#, IdenticalWithEvalError("(!! 0)")), // Double negation becomes unknown operation
            (r#"{"!!": [1]}"#, IdenticalWithEvalError("(!! 1)")), // Double negation becomes unknown operation
            (r#"{"!!": [""]}"#, IdenticalWithEvalError("(!! \"\")")), // Double negation becomes unknown operation
            (
                r#"{"!!": ["hello"]}"#,
                IdenticalWithEvalError("(!! \"hello\")"),
            ), // Double negation becomes unknown operation
            (r#"{"var": "field"}"#, IdenticalWithEvalError("field")), // Variable access converts to symbol
            (r#"{"if": [null, "yes", "no"]}"#, Error), // Null in JSONLogic expression should be rejected
            // JSONLogic syntactic sugar - unary operators without arrays (roundtrip normalizes)
            (r#"{"!": true}"#, SemanticallyEquivalent("(not #t)")), // Unary NOT without array
            (r#"{"!": false}"#, SemanticallyEquivalent("(not #f)")), // Unary NOT without array
            (r#"{"-": 2}"#, SemanticallyEquivalent("(- 2)")),       // Unary minus
            (r#"{"-": -2}"#, SemanticallyEquivalent("(- -2)")),     // Unary minus of negative
            // Type coercion edge cases (these should now fail due to strict typing)
            (
                r#"{"==": [1, "1"]}"#,
                IdenticalWithEvalError("(equal? 1 \"1\")"),
            ), // Type coercion rejected: number vs string
            (
                r#"{"==": [0, false]}"#,
                IdenticalWithEvalError("(equal? 0 #f)"),
            ), // Type coercion rejected: number vs boolean
            // Strict equality operators (these become unknown operations since they're not Scheme builtins)
            (r#"{"===": [1, 1]}"#, IdenticalWithEvalError("(=== 1 1)")), // Strict equality becomes unknown operation
            (
                r#"{"===": [1, "1"]}"#,
                IdenticalWithEvalError("(=== 1 \"1\")"),
            ), // Strict equality becomes unknown operation
            (r#"{"!==": [1, 2]}"#, IdenticalWithEvalError("(!== 1 2)")), // Strict not-equal becomes unknown operation
            // Between operations (chained comparisons)
            (r#"{"<": [1, 2, 3]}"#, Identical("(< 1 2 3)")), // Between exclusive (1 < 2 < 3)
            (r#"{"<": [1, 1, 3]}"#, Identical("(< 1 1 3)")), // Between exclusive fails at equality
            (r#"{"<=": [1, 2, 3]}"#, Identical("(<= 1 2 3)")), // Between inclusive (1 <= 2 <= 3)
            (r#"{"<=": [1, 1, 3]}"#, Identical("(<= 1 1 3)")), // Between inclusive allows equality
            // Array literals become list constructor calls (data, not executable code)
            (r#"[1, 2, 3]"#, Identical("(list 1 2 3)")), // Array literal converts to list call
            // Operations with array arguments (arrays become list constructors as data)
            (
                r#"{"and": [true, [1, 2]]}"#,
                IdenticalWithEvalError("(and #t (list 1 2))"),
            ), // Operation with array argument
            (
                r#"{"unknown": [[1, 2], 3]}"#,
                IdenticalWithEvalError("(unknown (list 1 2) 3)"),
            ), // Unknown operation with array argument
            (
                r#"{"test": [42, [], "end"]}"#,
                IdenticalWithEvalError(r#"(test 42 (list) "end")"#),
            ), // Mixed arguments including empty array
            // Complex nested array structures
            (
                r#"[[1, 2], [3, 4]]"#,
                Identical("(list (list 1 2) (list 3 4))"),
            ), // Nested arrays - should become nested list constructor calls
            (
                r#"[[], [1], [1, 2]]"#,
                Identical("(list (list) (list 1) (list 1 2))"),
            ), // Arrays with different lengths
            (r#"[[[]]]"#, Identical("(list (list (list)))")), // Triply nested empty arrays
            (r#"[1, [2, [3]]]"#, Identical("(list 1 (list 2 (list 3)))")), // Right-nested structure
            (r#"[[[1], 2], 3]"#, Identical("(list (list (list 1) 2) 3)")), // Left-nested structure
            // Arrays that could be mistaken for operator calls if not using list constructors
            (r#"["+", 1, 2]"#, Identical(r#"(list "+" 1 2)"#)), // Would be (+ 1 2) if not using list constructor
            (
                r#"["if", true, "yes", "no"]"#,
                Identical(r#"(list "if" #t "yes" "no")"#),
            ), // Would be if statement if not using list constructor
            (
                r#"["and", true, false]"#,
                Identical(r#"(list "and" #t #f)"#),
            ), // Would be logical and if not using list constructor
            (r#"["not", true]"#, Identical(r#"(list "not" #t)"#)), // Would be negation if not using list constructor
            (r#"["equal?", 1, 1]"#, Identical(r#"(list "equal?" 1 1)"#)), // Would be equality test if not using list constructor
            // Arrays with Scheme builtin names that should remain as data
            (
                r#"["car", "cdr", "cons"]"#,
                Identical(r#"(list "car" "cdr" "cons")"#),
            ),
            (
                r#"["define", "lambda", "let"]"#,
                Identical(r#"(list "define" "lambda" "let")"#),
            ),
            (
                r#"["quote", "unquote", "eval"]"#,
                Identical(r#"(list "quote" "unquote" "eval")"#),
            ),
            // Operations with nested array arguments
            (
                r#"{"test_nested": [[1, 2]]}"#,
                IdenticalWithEvalError("(test_nested (list 1 2))"),
            ),
            (
                r#"{"fn": [[1], [2, 3]]}"#,
                IdenticalWithEvalError("(fn (list 1) (list 2 3))"),
            ),
            (
                r#"{"mixed": [42, [1, 2], "hello"]}"#,
                IdenticalWithEvalError(r#"(mixed 42 (list 1 2) "hello")"#),
            ),
            (
                r#"{"complex": [true, [], [1], "end"]}"#,
                IdenticalWithEvalError(r#"(complex #t (list) (list 1) "end")"#),
            ),
            // Deeply nested structures with operations
            (
                r#"{"outer": [{"inner": [1, 2]}, [3, 4]]}"#,
                IdenticalWithEvalError("(outer (inner 1 2) (list 3 4))"),
            ),
            (
                r#"[{"op": [1]}, {"op2": [2]}]"#,
                IdenticalWithEvalError("(list (op 1) (op2 2))"),
            ),
            // Security-critical cases: Arrays with dangerous operation names stay as safe data
            (
                r#"["set!", "x", 123]"#,
                Identical(r#"(list "set!" "x" 123)"#),
            ), // Would modify variable if not using list constructor
            (
                r#"["eval", "(+ 1 2)"]"#,
                Identical(r#"(list "eval" "(+ 1 2)")"#),
            ), // Would eval code if not using list constructor
            (
                r#"["system", "rm -rf /"]"#,
                Identical(r#"(list "system" "rm -rf /")"#),
            ), // Would execute system command if not using list constructor
            (
                r#"["load", "dangerous-file.scm"]"#,
                Identical(r#"(list "load" "dangerous-file.scm")"#),
            ), // Would load file if not using list constructor
            // Complex nested lambda-like structures
            (
                r#"["lambda", ["x"], ["*", "x", "x"]]"#,
                Identical(r#"(list "lambda" (list "x") (list "*" "x" "x"))"#),
            ),
        ];

        run_data_driven_tests(&test_cases);
    }

    /// Helper function to test AST equivalence and roundtrip (shared by Identical and IdenticalWithEvalError)
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
                    match eval(&jsonlogic_ast, &mut create_global_env()) {
                        Ok(_) => {} // Good
                        Err(e) => panic!("Evaluation failed for {}: {:?}", jsonlogic, e),
                    }
                }
                (Ok(jsonlogic_ast), IdenticalWithEvalError(expected_scheme)) => {
                    test_ast_equivalence_and_roundtrip(jsonlogic, &jsonlogic_ast, expected_scheme);
                    // Verify that evaluation actually fails as expected
                    match eval(&jsonlogic_ast, &mut create_global_env()) {
                        Ok(result) => panic!(
                            "Expected evaluation to fail for {}, but got: {}",
                            jsonlogic, result
                        ),
                        Err(_) => {} // Expected failure
                    }
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
