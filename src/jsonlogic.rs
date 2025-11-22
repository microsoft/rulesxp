use crate::Error;
use crate::MAX_PARSE_DEPTH;
use crate::ast::{Value, is_valid_symbol};
use crate::builtinops::{BuiltinOp, find_jsonlogic_op, find_scheme_op, get_list_op, get_quote_op};
use crate::evaluator::Arity;

/// Indicates the compilation context for JSON values
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CompilationContext {
    /// Normal JSONLogic compilation - objects become operations, arrays become lists
    Normal,
    /// Array element context - used for elements inside JSONLogic arrays (operations still work)
    ArrayElement,
    /// Quote context - everything becomes literal data, no operations compiled
    Quote,
}

/// Parse JSONLogic expression into AST value for evaluation
pub fn parse_jsonlogic(input: &str) -> Result<Value, Error> {
    let json_value: serde_json::Value =
        serde_json::from_str(input).map_err(|e| Error::ParseError(format!("Invalid JSON: {e}")))?;

    compile_json_to_ast(json_value)
}

/// Compile a serde_json::Value to AST value
fn compile_json_to_ast(json: serde_json::Value) -> Result<Value, Error> {
    compile_json_to_ast_with_context(json, CompilationContext::Normal, 0)
}

fn compile_json_to_ast_with_context(
    json: serde_json::Value,
    context: CompilationContext,
    depth: usize,
) -> Result<Value, Error> {
    if depth >= MAX_PARSE_DEPTH {
        return Err(Error::ParseError(format!(
            "JSONLogic expression too deeply nested (max depth: {MAX_PARSE_DEPTH})"
        )));
    }
    match json {
        // Primitives
        serde_json::Value::Null => Err(Error::ParseError(
            "null values are not supported in this JSONLogic implementation".into(),
        )),
        serde_json::Value::Bool(b) => Ok(Value::Bool(b)),
        serde_json::Value::Number(n) => {
            if let Some(i) = n.as_i64() {
                Ok(Value::Number(i))
            } else {
                Err(Error::ParseError(format!(
                    "Number too large or not integer: {n}"
                )))
            }
        }
        serde_json::Value::String(s) => Ok(Value::String(s)),
        serde_json::Value::Array(arr) => {
            // Determine context for array elements
            let element_context = match context {
                CompilationContext::Quote => CompilationContext::Quote, // Quote context propagates
                _ => CompilationContext::ArrayElement, // Normal/ArrayElement becomes ArrayElement
            };

            let converted: Vec<Value> = arr
                .into_iter()
                .map(|v| compile_json_to_ast_with_context(v, element_context, depth + 1))
                .collect::<Result<Vec<_>, _>>()?;

            match context {
                CompilationContext::Quote => {
                    // In quote context, arrays become literal list data without "list" symbol
                    // This matches the Scheme representation: (quote ("+" 1 2)) -> just the list elements
                    Ok(Value::List(converted))
                }
                _ => {
                    // Arrays always become list operations in JSONLogic
                    let list_op = get_list_op();
                    Ok(Value::PrecompiledOp {
                        op: list_op,
                        op_id: list_op.scheme_id.into(),
                        args: converted,
                    })
                }
            }
        }
        serde_json::Value::Object(obj) => {
            let (operator, operands) = {
                let mut iter = obj.into_iter();
                // Attempt to get two elements from this object - hoping to get only 1 item back
                match (iter.next(), iter.next()) {
                    (Some((op, val)), None) => (op, val), // Exactly one item
                    _ => {
                        return Err(Error::ParseError(
                            "JSONLogic operations must have exactly one operator".into(),
                        ));
                    }
                }
            };

            match context {
                CompilationContext::Quote => {
                    // In quote context, only {"var": "symbol"} objects are allowed
                    // All other objects (operations) are forbidden to ensure canonical list representation
                    if operator == "var" {
                        // {"var": "symbol"} becomes a symbol in quote context
                        match operands {
                            serde_json::Value::String(var_name) if is_valid_symbol(&var_name) => {
                                Ok(Value::Symbol(var_name))
                            }
                            _ => Err(Error::ParseError(
                                "Variable must be a valid symbol string".into(),
                            )),
                        }
                    } else {
                        // Reject all other object form operations in quote context
                        Err(Error::ParseError(format!(
                            "Object form operations like '{{\"{operator}\":...}}' are not allowed in quote context. Use list form like '[\"{operator}\", ...]' instead"
                        )))
                    }
                }
                CompilationContext::Normal | CompilationContext::ArrayElement => {
                    // Normal compilation context - compile as operation
                    compile_jsonlogic_operation(&operator, operands, depth)
                }
            }
        }
    }
}

/// Compile JSONLogic operations to S-expression function calls
fn compile_jsonlogic_operation(
    operator: &str,
    operands: serde_json::Value,
    depth: usize,
) -> Result<Value, Error> {
    // Helper function to extract operands as a list, ignoring arity checks
    let extract_operand_list = |operands: serde_json::Value| -> Result<Vec<Value>, Error> {
        match operands {
            serde_json::Value::Array(arr) => {
                // Convert each operand - arrays that appear as operands should use list constructors as data
                // (because they represent data values, not argument lists to be expanded)
                // Non-arrays are scalar arguments and should not use list constructors
                arr.into_iter()
                    .map(|v| {
                        let context = if matches!(v, serde_json::Value::Array(_)) {
                            CompilationContext::ArrayElement
                        } else {
                            CompilationContext::Normal
                        };
                        compile_json_to_ast_with_context(v, context, depth + 1)
                    })
                    .collect::<Result<Vec<_>, _>>()
            }
            // Single operand - use list constructor if it's an array (data), don't modify scalars
            single => {
                let context = if matches!(single, serde_json::Value::Array(_)) {
                    CompilationContext::ArrayElement
                } else {
                    CompilationContext::Normal
                };
                Ok(vec![compile_json_to_ast_with_context(
                    single,
                    context,
                    depth + 1,
                )?])
            }
        }
    };

    // Helper function to create PrecompiledOp from a known builtin operation
    let create_precompiled_op = |builtin_op: &'static BuiltinOp, args: Vec<Value>| -> Value {
        Value::PrecompiledOp {
            op: builtin_op,
            op_id: builtin_op.scheme_id.into(),
            args,
        }
    };

    // Special cases that need manual handling
    // Note: In this implementation == is an alias to === and != to !==. While these operations normally have
    // significantly different semantics, in this implementation, there is no type coercion so their behavior is identical!
    match operator {
        // !== and != need special handling with binary arity validation, since equal? takes arbitrary arguments
        "!==" | "!=" => {
            let args = extract_operand_list(operands)?;
            // Validate that we have exactly 2 arguments for not-equal operation
            Arity::Exact(2).validate(args.len())?;

            let equal_builtin = find_jsonlogic_op("===").expect("=== builtin should exist");
            let equal_op = create_precompiled_op(equal_builtin, args);

            let not_builtin = find_jsonlogic_op("!").expect("! builtin should exist");
            Ok(create_precompiled_op(not_builtin, vec![equal_op]))
        }

        // == is an alias for === (handled here to avoid duplicate registry entries)
        "==" => {
            let args = extract_operand_list(operands)?;
            let equal_builtin = find_jsonlogic_op("===").expect("=== builtin should exist");
            // Validate arity using the builtin operation's definition
            equal_builtin.validate_arity(args.len())?;
            Ok(create_precompiled_op(equal_builtin, args))
        }

        // Variable access (JSONLogic specific)
        "var" => match operands {
            serde_json::Value::String(var_name) if is_valid_symbol(&var_name) => {
                Ok(Value::Symbol(var_name))
            }
            _ => Err(Error::ParseError(
                "Variable must be a valid symbol string".into(),
            )),
        },

        // Quote special form - CRITICAL: preserve quoted content as literal data
        "scheme-quote" => {
            // Quote must have exactly one operand and must NOT compile/evaluate it
            let operand = match operands {
                serde_json::Value::Array(arr) => match arr.as_slice() {
                    [single_operand] => single_operand.clone(),
                    _ => {
                        return Err(Error::ParseError("quote requires one operand".into()));
                    }
                },
                single_operand => single_operand, // Single operand without array wrapper
            };

            // Convert the operand to literal data WITHOUT compilation/evaluation
            // This preserves the quoted content as pure data
            let quoted_data =
                compile_json_to_ast_with_context(operand, CompilationContext::Quote, depth + 1)?;

            // Create a PrecompiledOp wrapper to preserve quote information for roundtrip
            // This allows us to distinguish quoted data from regular list data
            let quote_op = get_quote_op();
            Ok(Value::PrecompiledOp {
                op: quote_op,
                op_id: quote_op.scheme_id.into(),
                args: vec![quoted_data],
            })
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
                    Err(Error::ParseError(format!(
                        "JSONLogic operator '{operator}' is not supported. Use the JSONLogic equivalent instead (e.g., use '!' instead of 'not')."
                    )))
                } else {
                    // Operation not in registry and not a Scheme builtin - emit as regular list for custom operations
                    // But first validate that the operator name is a valid symbol
                    if !is_valid_symbol(operator) {
                        return Err(Error::ParseError(format!(
                            "Invalid operator name: '{operator}'"
                        )));
                    }
                    let args = extract_operand_list(operands)?;
                    let mut result = vec![Value::Symbol(operator.into())];
                    result.extend(args);
                    Ok(Value::List(result))
                }
            }
        }
    }
}

/// Convert an AST value back to JSONLogic format
pub fn ast_to_jsonlogic(value: &Value) -> Result<String, Error> {
    let json_value = ast_to_json_value(value)?;
    serde_json::to_string(&json_value)
        .map_err(|e| Error::EvalError(format!("Failed to serialize JSON: {e}")))
}

/// Convert an AST value to serde_json::Value for JSONLogic output
fn ast_to_json_value(value: &Value) -> Result<serde_json::Value, Error> {
    ast_to_json_value_with_context(value, false)
}

/// Convert an AST value to serde_json::Value with optional quote context
fn ast_to_json_value_with_context(
    value: &Value,
    in_quote_context: bool,
) -> Result<serde_json::Value, Error> {
    match value {
        Value::Number(n) => Ok(serde_json::Value::Number(serde_json::Number::from(*n))),
        Value::String(s) => Ok(serde_json::Value::String(s.clone())),
        Value::Bool(b) => Ok(serde_json::Value::Bool(*b)),
        Value::Symbol(s) => Ok(serde_json::json!({"var": s})),
        Value::List(list) if list.is_empty() => Ok(serde_json::Value::Array(vec![])),
        Value::List(list) => {
            if in_quote_context {
                // In quote context, lists always become arrays
                let converted: Result<Vec<serde_json::Value>, Error> = list
                    .iter()
                    .map(|v| ast_to_json_value_with_context(v, true))
                    .collect();
                Ok(serde_json::Value::Array(converted?))
            } else if let [Value::Symbol(op), args @ ..] = list.as_slice() {
                let args: Result<Vec<serde_json::Value>, Error> =
                    args.iter().map(ast_to_json_value).collect();
                let args = args?;

                match op.as_str() {
                    "list" => Ok(serde_json::Value::Array(args)),
                    _ => {
                        let jsonlogic_op = find_scheme_op(op)
                            .map_or(op.as_str(), |builtin_op| builtin_op.jsonlogic_id);
                        Ok(serde_json::json!({jsonlogic_op: args}))
                    }
                }
            } else {
                let converted: Result<Vec<serde_json::Value>, Error> =
                    list.iter().map(ast_to_json_value).collect();
                Ok(serde_json::Value::Array(converted?))
            }
        }
        Value::BuiltinFunction { .. } => {
            Err(Error::EvalError("Cannot convert builtin function".into()))
        }
        Value::PrecompiledOp { op, args, .. } => {
            if in_quote_context {
                return Err(Error::EvalError("PrecompiledOp in quote context".into()));
            }

            match op.scheme_id {
                "list" => {
                    let converted: Result<Vec<serde_json::Value>, Error> =
                        args.iter().map(ast_to_json_value).collect();
                    Ok(serde_json::Value::Array(converted?))
                }
                "quote" => match args.as_slice() {
                    [single_arg] => {
                        let quoted_content = ast_to_json_value_with_context(single_arg, true)?;
                        Ok(serde_json::json!({"scheme-quote": [quoted_content]}))
                    }
                    _ => Err(Error::EvalError("Quote needs one argument".to_owned())),
                },
                _ => {
                    let converted_args: Result<Vec<serde_json::Value>, Error> =
                        args.iter().map(ast_to_json_value).collect();
                    Ok(serde_json::json!({op.jsonlogic_id: converted_args?}))
                }
            }
        }
        Value::Function { .. } => Err(Error::EvalError("Cannot convert user function".to_owned())),
        Value::Unspecified => Err(Error::EvalError(
            "Cannot convert unspecified value".to_owned(),
        )),
    }
}

#[cfg(all(test, feature = "scheme"))]
#[expect(clippy::unwrap_used)] // test code OK
mod tests {
    use core::panic;

    use super::*;
    use crate::evaluator::{create_global_env, eval};
    use crate::scheme::parse_scheme;

    #[derive(Debug)]
    enum TestResult {
        Identical(&'static str),
        IdenticalWithEvalError(&'static str), // Parsing succeeds, test AST equivalence, but evaluation must fail
        SemanticallyEquivalent(&'static str),
        Error,
        SpecificError(&'static str), // Parsing should fail with an error message containing this string
    }
    use TestResult::*;

    #[test]
    #[expect(clippy::too_many_lines)] // Comprehensive test coverage is intentionally thorough
    fn test_jsonlogic_to_scheme_equivalence() {
        // Test cases as tuples: (jsonlogic, scheme_equivalent)
        let test_cases = vec![
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
            // Equality operations - === is canonical, == is alias
            (r#"{"===": [1, 2]}"#, Identical("(equal? 1 2)")),
            (r#"{"==": [1, 2]}"#, SemanticallyEquivalent("(equal? 1 2)")),
            (r#"{">": [5, 3]}"#, Identical("(> 5 3)")),
            (r#"{"<": [2, 5]}"#, Identical("(< 2 5)")),
            (r#"{">=": [5, 5]}"#, Identical("(>= 5 5)")),
            (r#"{"<=": [3, 5]}"#, Identical("(<= 3 5)")),
            // Logical operations
            (r#"{"and": [true, false]}"#, Identical("(and #t #f)")),
            (r#"{"or": [false, false]}"#, Identical("(or #f #f)")),
            (r#"{"!": [true]}"#, Identical("(not #t)")),
            // Not-equal operations - !== is canonical, != is alias (both expand to (not (equal? ...)))
            (
                r#"{"!==": [1, 2]}"#,
                SemanticallyEquivalent("(not (equal? 1 2))"),
            ),
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
            // String operations
            (
                r#"{"cat": "hello"}"#,
                SemanticallyEquivalent(r#"(string-append "hello")"#),
            ),
            (
                r#"{"cat": ["hello", " ", "world"]}"#,
                Identical(r#"(string-append "hello" " " "world")"#),
            ),
            (r#"{"cat": []}"#, Identical("(string-append)")),
            // Math operations
            (r#"{"max": [1, 2, 3]}"#, Identical("(max 1 2 3)")),
            (r#"{"max": 5}"#, SemanticallyEquivalent("(max 5)")),
            (r#"{"min": [1, 2, 3]}"#, Identical("(min 1 2 3)")),
            (r#"{"min": 5}"#, SemanticallyEquivalent("(min 5)")),
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
            ("null", Error), // Null values should be rejected
            (r#"{"!==": [1]}"#, SpecificError("ArityError")), // Not equal with wrong arity should fail
            (r#"{"!==": [1, 2, 3]}"#, SpecificError("ArityError")), // Not equal with too many args should fail
            (r#"{"!=": [1]}"#, SpecificError("ArityError")), // != alias also fails with wrong arity
            (r#"{"!=": [1, 2, 3]}"#, SpecificError("ArityError")), // != alias also fails with too many args
            (r#"{"if": [true, "yes"]}"#, SpecificError("ArityError")), // If with wrong arity should fail
            ("invalid json", Error),                                   // Invalid JSON should fail
            (r#"{"and": true, "or": false}"#, Error), // Multiple keys in object should fail
            // Quote context error cases - object form operations should be rejected
            (
                r#"{"scheme-quote": [{"+": [1, 2]}]}"#,
                SpecificError("Object form operations"),
            ),
            (
                r#"{"scheme-quote": [{"if": [true, "yes", "no"]}]}"#,
                SpecificError("not allowed in quote context"),
            ),
            (
                r#"{"scheme-quote": [{"not": true}]}"#,
                SpecificError("Object form operations"),
            ),
            (
                r#"{"scheme-quote": [{"and": [true, false]}]}"#,
                SpecificError("not allowed in quote context"),
            ),
            (
                r#"{"scheme-quote": [{"car": [1, 2, 3]}]}"#,
                SpecificError("Object form operations"),
            ),
            // Nested object form operations should also be rejected
            (
                r#"{"scheme-quote": [["list", {"+": [1, 2]}]]}"#,
                SpecificError("Object form operations"),
            ),
            // Empty string variable names should be rejected
            (
                r#"{"scheme-quote": [{"var": ""}]}"#,
                SpecificError("Variable must be a valid symbol string"),
            ),
            // Invalid operator names should be rejected
            (
                r#"{"invalid op": [1, 2]}"#,
                SpecificError("Invalid operator name"),
            ),
            (
                r#"{"123invalid": [1, 2]}"#,
                SpecificError("Invalid operator name"),
            ),
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
            // Type coercion edge cases - our language rejects type coercion with strict typing
            (
                r#"{"===": [1, "1"]}"#,
                IdenticalWithEvalError("(equal? 1 \"1\")"),
            ), // Strict equality: different types cause type error (no coercion)
            (
                r#"{"===": [0, false]}"#,
                IdenticalWithEvalError("(equal? 0 #f)"),
            ), // Strict equality: different types cause type error (no coercion)
            // Test that == alias works the same as === (but roundtrips to === canonical form)
            // Type mismatch cases are handled by the alias behavior - no special tests needed
            // Test additional === cases (canonical equality)
            (r#"{"===": [1, 1]}"#, Identical("(equal? 1 1)")), // Canonical strict equality
            (r#"{"===": [true, true]}"#, Identical("(equal? #t #t)")), // Boolean equality
            (
                r#"{"===": ["hello", "hello"]}"#,
                Identical("(equal? \"hello\" \"hello\")"),
            ), // String equality
            // !== expands to (not (equal? ...)) so it won't roundtrip identically
            // Type mismatch cases are handled by the underlying equal? behavior
            // != type mismatch cases are handled by the alias behavior - no special tests needed
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
            // Arrays in JSON are not function calls in Scheme - they become list constructor calls
            (
                r#"["eval", "(+ 1 2)"]"#,
                Identical(r#"(list "eval" "(+ 1 2)")"#),
            ),
            (
                r#"["load", "dangerous-file.scm"]"#,
                Identical(r#"(list "load" "dangerous-file.scm")"#),
            ),
            // ===== QUOTE OPERATION TESTS (CRITICAL FOR EVALUATION CONTROL) =====
            // Quote should preserve content as literal data without PrecompiledOps/Functions
            (
                r#"{"scheme-quote": ["hello"]}"#,
                Identical(r#"(quote "hello")"#),
            ),
            (r#"{"scheme-quote": [42]}"#, Identical("(quote 42)")),
            (r#"{"scheme-quote": [true]}"#, Identical("(quote #t)")),
            (
                r#"{"scheme-quote": [[1, 2, 3]]}"#,
                Identical("(quote (1 2 3))"),
            ),
            // Quote should prevent evaluation of operations (using list form only)
            (
                r#"{"scheme-quote": [["+", 1, 2]]}"#,
                Identical("(quote (\"+\" 1 2))"),
            ),
            (
                r#"{"scheme-quote": [["not", true]]}"#,
                Identical("(quote (\"not\" #t))"),
            ),
            (
                r#"{"scheme-quote": [["if", true, "yes", "no"]]}"#,
                Identical(r#"(quote ("if" #t "yes" "no"))"#),
            ),
            // Quote with nested operations (should all become data)
            (
                r#"{"scheme-quote": [["car", ["list", 1, 2, 3]]]}"#,
                Identical(r#"(quote ("car" ("list" 1 2 3)))"#),
            ),
            // Quote with arrays containing operations
            (
                r#"{"scheme-quote": [[["+", 1, 2], ["-", 3, 1]]]}"#,
                Identical(r#"(quote (("+" 1 2) ("-" 3 1)))"#),
            ),
            // Quote preserves symbol structure ({"var": "x"} is allowed in quotes)
            (
                r#"{"scheme-quote": [{"var": "x"}]}"#,
                Identical("(quote x)"),
            ),
            (
                r#"{"scheme-quote": [["and", true, false]]}"#,
                Identical(r#"(quote ("and" #t #f))"#),
            ),
            (
                r#"{"scheme-quote": [[{"var": "func"}, 1, 2]]}"#,
                Identical(r#"(quote (func 1 2))"#),
            ),
            (
                r#"{"scheme-quote": [["list", {"var": "symbol"}, 1, 2]]}"#,
                Identical(r#"(quote ("list" symbol 1 2))"#),
            ), // List with symbol in quote context
            // Complex nested lambda-like structures
            (
                r#"["lambda", ["x"], ["*", "x", "x"]]"#,
                Identical(r#"(list "lambda" (list "x") (list "*" "x" "x"))"#),
            ),
        ];

        run_data_driven_tests(&test_cases);
    }

    #[test]
    fn test_jsonlogic_depth_limits() {
        // Create depth limit test strings
        let arrays_under_limit = format!(
            "{}{}{}",
            "[".repeat(MAX_PARSE_DEPTH - 1),
            r#"{"var": "unbound"}"#,
            "]".repeat(MAX_PARSE_DEPTH - 1)
        );
        let objects_under_limit = format!(
            "{}{}{}",
            r#"{"op": "#.repeat(MAX_PARSE_DEPTH - 1),
            r#"{"var": "unbound"}"#,
            "}".repeat(MAX_PARSE_DEPTH - 1)
        );
        let deep_arrays_at_limit = format!(
            "{}{}{}",
            "[".repeat(MAX_PARSE_DEPTH),
            "1",
            "]".repeat(MAX_PARSE_DEPTH)
        );
        let deep_objects_at_limit = format!(
            "{}{}{}",
            r#"{"op": "#.repeat(MAX_PARSE_DEPTH),
            r#"{"end": 1}"#,
            "}".repeat(MAX_PARSE_DEPTH)
        );

        let depth_test_cases = vec![
            // At/over limit should fail with specific depth error
            (
                deep_arrays_at_limit.as_str(),
                SpecificError("too deeply nested"),
            ),
            (
                deep_objects_at_limit.as_str(),
                SpecificError("too deeply nested"),
            ),
        ];

        run_data_driven_tests(&depth_test_cases);

        // Test that under-limit cases parse successfully (separate verification)
        let arrays_result = parse_jsonlogic(&arrays_under_limit);
        let objects_result = parse_jsonlogic(&objects_under_limit);
        assert!(
            arrays_result.is_ok(),
            "Arrays just under depth limit should parse successfully"
        );
        assert!(
            objects_result.is_ok(),
            "Objects just under depth limit should parse successfully"
        );
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
            "Roundtrip failed: {jsonlogic} -> {back_to_json} (expected {jsonlogic})"
        );
    }

    /// Helper function to run data-driven tests
    fn run_data_driven_tests(test_cases: &[(&str, TestResult)]) {
        for (jsonlogic, expected_result) in test_cases {
            println!("Testing JSONLogic: {jsonlogic}, expected: {expected_result:?}");

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
                    if let Ok(result) = eval(&jsonlogic_ast, &mut create_global_env()) {
                        panic!(
                            "Expected evaluation to fail for {}, but got: {}",
                            jsonlogic, result
                        )
                    }
                    // Expected failure
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
                (Err(e), SpecificError(expected_error_text)) => {
                    let error_msg = format!("{e:?}");
                    assert!(
                        error_msg.contains(expected_error_text),
                        "Error message should contain '{expected_error_text}', but got: {error_msg}"
                    );
                }
                (Ok(_), SpecificError(expected_error_text)) => {
                    panic!(
                        "Expected error containing '{}' for JSONLogic '{}', but parsing succeeded",
                        expected_error_text, jsonlogic
                    );
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
