use crate::SchemeError;
use crate::ast::Value;
use crate::builtinops::{
    Arity, BUILTIN_OPS_JSONLOGIC, find_builtin_op_by_scheme_id, map_scheme_id_to_jsonlogic,
};
use serde_json;

/// Parse JSONLogic expression into our Value enum for evaluation
pub fn parse_jsonlogic(input: &str) -> Result<Value, SchemeError> {
    let json_value: serde_json::Value = serde_json::from_str(input)
        .map_err(|e| SchemeError::ParseError(format!("Invalid JSON: {}", e)))?;

    convert_json_to_value(json_value)
}

/// Convert a serde_json::Value to our internal Value enum
fn convert_json_to_value(json: serde_json::Value) -> Result<Value, SchemeError> {
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
                .map(convert_json_to_value)
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
            convert_jsonlogic_operation(&operator, operands)
        }
    }
}

/// Convert JSONLogic operations to S-expression function calls
fn convert_jsonlogic_operation(
    operator: &str,
    operands: serde_json::Value,
) -> Result<Value, SchemeError> {
    // Helper function to extract operands as a list, ignoring arity checks
    let extract_operand_list = |operands: serde_json::Value| -> Result<Vec<Value>, SchemeError> {
        let converted = convert_json_to_value(operands)?;
        match converted {
            Value::List(list) => Ok(list),
            // If it's a single value, wrap it in a list
            single_value => Ok(vec![single_value]),
        }
    };

    // Helper function to create PrecompiledOp if the operation exists
    let create_precompiled_op = |scheme_op_name: &str, args: Vec<Value>| -> Value {
        if let Some(builtin_op) = find_builtin_op_by_scheme_id(scheme_op_name) {
            Value::PrecompiledOp {
                op: builtin_op,
                op_name: scheme_op_name.to_string(),
                args,
            }
        } else {
            // Fallback to regular list if not a builtin operation
            let mut result = vec![Value::Symbol(scheme_op_name.to_string())];
            result.extend(args);
            Value::List(result)
        }
    };

    // Special cases that need manual handling
    match operator {
        // != needs special handling with binary arity validation, since equal? takes arbitrary arguments
        "!=" => {
            let args = extract_operand_list(operands)?;
            // Validate that we have exactly 2 arguments for != operation
            Arity::Exact(2).validate(args.len())?;
            let equal_op = create_precompiled_op("equal?", args);
            Ok(create_precompiled_op("not", vec![equal_op]))
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
            // Check if this operation is in the JSONLogic registry and has a builtin implementation
            if let Some(scheme_id_and_op) =
                BUILTIN_OPS_JSONLOGIC.get(operator).and_then(|scheme_id| {
                    find_builtin_op_by_scheme_id(scheme_id).map(|op| (*scheme_id, op))
                })
            {
                let (scheme_id, builtin_op) = scheme_id_and_op;
                let args = extract_operand_list(operands)?;

                // Validate arity using the builtin operation's definition
                builtin_op.validate_arity(args.len())?;

                Ok(create_precompiled_op(scheme_id, args))
            } else {
                // Operation not in registry or no builtin found - emit as regular list
                let scheme_id = BUILTIN_OPS_JSONLOGIC.get(operator).unwrap_or(&operator);
                let args = extract_operand_list(operands)?;
                let mut result = vec![Value::Symbol(scheme_id.to_string())];
                result.extend(args);
                Ok(Value::List(result))
            }
        }
    }
}

/// Convert a Value back to JSONLogic format
pub fn value_to_jsonlogic(value: &Value) -> Result<String, SchemeError> {
    let json_value = value_to_json_value(value)?;
    serde_json::to_string(&json_value)
        .map_err(|e| SchemeError::EvalError(format!("Failed to serialize JSON: {}", e)))
}

/// Convert a Value to serde_json::Value for JSONLogic output
fn value_to_json_value(value: &Value) -> Result<serde_json::Value, SchemeError> {
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
                    list[1..].iter().map(value_to_json_value).collect();
                let args = args?;

                // Convert Scheme operator names back to JSONLogic operators
                let jsonlogic_op = map_scheme_id_to_jsonlogic(op);

                // Handle different argument patterns
                match args.len() {
                    0 => Err(SchemeError::EvalError(format!(
                        "Operation {} requires arguments",
                        op
                    ))),
                    _ => {
                        // Always use array format for all operations
                        Ok(serde_json::json!({jsonlogic_op: args}))
                    }
                }
            } else {
                // Convert list elements
                let converted: Result<Vec<serde_json::Value>, SchemeError> =
                    list.iter().map(value_to_json_value).collect();
                Ok(serde_json::Value::Array(converted?))
            }
        }
        Value::BuiltinFunction(_) => Err(SchemeError::EvalError(
            "Cannot convert builtin function to JSONLogic".to_string(),
        )),
        Value::PrecompiledOp { op_name, args, .. } => {
            // Convert Scheme operator names back to JSONLogic operators
            let jsonlogic_op = map_scheme_id_to_jsonlogic(op_name);

            // Convert arguments
            let converted_args: Result<Vec<serde_json::Value>, SchemeError> =
                args.iter().map(value_to_json_value).collect();
            let args = converted_args?;

            // Handle different argument patterns
            match args.len() {
                0 => Err(SchemeError::EvalError(format!(
                    "Operation {} requires arguments",
                    op_name
                ))),
                _ => {
                    // Always use array format for all operations
                    Ok(serde_json::json!({jsonlogic_op: args}))
                }
            }
        }
        Value::Function { .. } => Err(SchemeError::EvalError(
            "Cannot convert user function to JSONLogic".to_string(),
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_primitives() {
        assert_eq!(parse_jsonlogic("true").unwrap(), Value::Bool(true));
        assert_eq!(parse_jsonlogic("false").unwrap(), Value::Bool(false));
        assert_eq!(parse_jsonlogic("42").unwrap(), Value::Number(42));
        assert_eq!(
            parse_jsonlogic("\"hello\"").unwrap(),
            Value::String("hello".to_string())
        );

        // null values are now rejected
        assert!(parse_jsonlogic("null").is_err());
    }

    #[test]
    fn test_parse_logical_operations() {
        // {"and": [true, false]}
        let result = parse_jsonlogic(r#"{"and": [true, false]}"#).unwrap();
        assert_eq!(
            result.to_uncompiled_form(),
            Value::List(vec![
                Value::Symbol("and".to_string()),
                Value::Bool(true),
                Value::Bool(false)
            ])
        );

        // {"or": [true, false]}
        let result = parse_jsonlogic(r#"{"or": [true, false]}"#).unwrap();
        assert_eq!(
            result.to_uncompiled_form(),
            Value::List(vec![
                Value::Symbol("or".to_string()),
                Value::Bool(true),
                Value::Bool(false)
            ])
        );

        // {"!": [true]}
        let result = parse_jsonlogic(r#"{"!": [true]}"#).unwrap();
        assert_eq!(
            result.to_uncompiled_form(),
            Value::List(vec![Value::Symbol("not".to_string()), Value::Bool(true)])
        );
    }

    #[test]
    fn test_parse_comparisons() {
        // {"==": [1, 1]}
        let result = parse_jsonlogic(r#"{"==": [1, 1]}"#).unwrap();
        assert_eq!(
            result.to_uncompiled_form(),
            Value::List(vec![
                Value::Symbol("equal?".to_string()),
                Value::Number(1),
                Value::Number(1)
            ])
        );

        // {">": [2, 1]}
        let result = parse_jsonlogic(r#"{">": [2, 1]}"#).unwrap();
        assert_eq!(
            result.to_uncompiled_form(),
            Value::List(vec![
                Value::Symbol(">".to_string()),
                Value::Number(2),
                Value::Number(1)
            ])
        );
    }

    #[test]
    fn test_parse_arithmetic() {
        // {"+": [1, 2, 3]}
        let result = parse_jsonlogic(r#"{"+": [1, 2, 3]}"#).unwrap();
        assert_eq!(
            result.to_uncompiled_form(),
            Value::List(vec![
                Value::Symbol("+".to_string()),
                Value::Number(1),
                Value::Number(2),
                Value::Number(3)
            ])
        );
    }

    #[test]
    fn test_parse_var() {
        // {"var": "age"}
        let result = parse_jsonlogic(r#"{"var": "age"}"#).unwrap();
        assert_eq!(result, Value::Symbol("age".to_string()));
    }

    #[test]
    fn test_nested_operations() {
        // {"and": [{"var": "age"}, {">": [{"var": "age"}, 18]}]}
        let result =
            parse_jsonlogic(r#"{"and": [{"var": "age"}, {">": [{"var": "age"}, 18]}]}"#).unwrap();
        assert_eq!(
            result.to_uncompiled_form(),
            Value::List(vec![
                Value::Symbol("and".to_string()),
                Value::Symbol("age".to_string()),
                Value::List(vec![
                    Value::Symbol(">".to_string()),
                    Value::Symbol("age".to_string()),
                    Value::Number(18)
                ])
            ])
        );
    }

    #[test]
    fn test_arity_validation_and_registry() {
        // Test != with correct arity (2 arguments)
        let result = parse_jsonlogic(r#"{"!=": [1, 2]}"#).unwrap();
        assert!(matches!(result, Value::PrecompiledOp { .. }));

        // Test != with wrong arity (1 argument) - should fail
        assert!(parse_jsonlogic(r#"{"!=": [1]}"#).is_err());

        // Test != with wrong arity (3 arguments) - should fail
        assert!(parse_jsonlogic(r#"{"!=": [1, 2, 3]}"#).is_err());

        // Test operations from registry get proper arity validation
        // Test "!" (not) with correct arity
        let result = parse_jsonlogic(r#"{"!": [true]}"#).unwrap();
        assert!(matches!(result, Value::PrecompiledOp { .. }));

        // Test "if" with correct arity (exactly 3)
        let result = parse_jsonlogic(r#"{"if": [true, 1, 2]}"#).unwrap();
        assert!(matches!(result, Value::PrecompiledOp { .. }));

        // Test "if" with wrong arity (2 arguments) - should fail
        assert!(parse_jsonlogic(r#"{"if": [true, 1]}"#).is_err());

        // Test operations not in registry get emitted as lists
        let result = parse_jsonlogic(r#"{"unknown": [1, 2, 3]}"#).unwrap();
        assert_eq!(
            result,
            Value::List(vec![
                Value::Symbol("unknown".to_string()),
                Value::Number(1),
                Value::Number(2),
                Value::Number(3)
            ])
        );

        // Test that operations in registry but with wrong arity fail
        // Addition with too few args should fail based on builtin arity
        // Note: "+" has AtLeast(0) arity, so this should succeed
        let result = parse_jsonlogic(r#"{"+": []}"#).unwrap();
        assert!(matches!(result, Value::PrecompiledOp { .. }));
    }

    #[test]
    fn test_error_cases() {
        // Invalid JSON
        assert!(parse_jsonlogic("invalid json").is_err());

        // Multiple keys in object
        assert!(parse_jsonlogic(r#"{"and": true, "or": false}"#).is_err());

        // Unknown operator should now emit a regular list instead of failing
        let result = parse_jsonlogic(r#"{"unknown": [1, 2]}"#).unwrap();
        assert_eq!(
            result,
            Value::List(vec![
                Value::Symbol("unknown".to_string()),
                Value::Number(1),
                Value::Number(2)
            ])
        );
    }

    #[test]
    fn test_value_to_jsonlogic() {
        // Test primitives
        assert_eq!(value_to_jsonlogic(&Value::Bool(true)).unwrap(), "true");
        assert_eq!(value_to_jsonlogic(&Value::Bool(false)).unwrap(), "false");
        assert_eq!(value_to_jsonlogic(&Value::Number(42)).unwrap(), "42");
        assert_eq!(
            value_to_jsonlogic(&Value::String("hello".to_string())).unwrap(),
            "\"hello\""
        );

        // Test symbols (converted to var operations)
        assert_eq!(
            value_to_jsonlogic(&Value::Symbol("age".to_string())).unwrap(),
            r#"{"var":"age"}"#
        );

        // Test simple operations
        let and_op = Value::List(vec![
            Value::Symbol("and".to_string()),
            Value::Bool(true),
            Value::Bool(false),
        ]);
        assert_eq!(
            value_to_jsonlogic(&and_op).unwrap(),
            r#"{"and":[true,false]}"#
        );

        // Test unary operation (always uses array format)
        let not_op = Value::List(vec![Value::Symbol("not".to_string()), Value::Bool(true)]);
        assert_eq!(value_to_jsonlogic(&not_op).unwrap(), r#"{"!":[true]}"#);

        // Test equality operation
        let eq_op = Value::List(vec![
            Value::Symbol("equal?".to_string()),
            Value::Number(1),
            Value::Number(2),
        ]);
        assert_eq!(value_to_jsonlogic(&eq_op).unwrap(), r#"{"==":[1,2]}"#);
    }

    #[test]
    fn test_precompiled_op_roundtrip() {
        // Test that JSONLogic -> PrecompiledOp -> JSONLogic works correctly

        // Test arithmetic operation
        let original_json = r#"{"+":[1,2,3]}"#;
        let parsed = parse_jsonlogic(original_json).unwrap();
        // Verify we got a PrecompiledOp
        assert!(matches!(parsed, Value::PrecompiledOp { .. }));
        let back_to_json = value_to_jsonlogic(&parsed).unwrap();
        assert_eq!(back_to_json, original_json);

        // Test comparison operation
        let original_json = r#"{"==":[1,2]}"#;
        let parsed = parse_jsonlogic(original_json).unwrap();
        assert!(matches!(parsed, Value::PrecompiledOp { .. }));
        let back_to_json = value_to_jsonlogic(&parsed).unwrap();
        assert_eq!(back_to_json, original_json);

        // Test logical operation
        let original_json = r#"{"and":[true,false]}"#;
        let parsed = parse_jsonlogic(original_json).unwrap();
        assert!(matches!(parsed, Value::PrecompiledOp { .. }));
        let back_to_json = value_to_jsonlogic(&parsed).unwrap();
        assert_eq!(back_to_json, original_json);

        // Test unary operation
        let original_json = r#"{"!":[true]}"#;
        let parsed = parse_jsonlogic(original_json).unwrap();
        assert!(matches!(parsed, Value::PrecompiledOp { .. }));
        let back_to_json = value_to_jsonlogic(&parsed).unwrap();
        assert_eq!(back_to_json, original_json);

        // Test nested operations
        let original_json = r#"{"and":[{"var":"age"},{">":[{"var":"age"},18]}]}"#;
        let parsed = parse_jsonlogic(original_json).unwrap();
        assert!(matches!(parsed, Value::PrecompiledOp { .. }));
        let back_to_json = value_to_jsonlogic(&parsed).unwrap();
        assert_eq!(back_to_json, original_json);

        // Test "!=" semantic roundtrip (not exact)
        // JSONLogic {"!=": [a, b]} gets parsed into internal structure: (not (equal? a b))
        // When converted back to JSONLogic, it becomes {"!": [{"==": [a, b]}]}
        // This is semantically equivalent but not syntactically identical
        let original_json = r#"{"!=":[1,2]}"#;
        let parsed = parse_jsonlogic(original_json).unwrap();
        assert!(matches!(parsed, Value::PrecompiledOp { .. }));
        let back_to_json = value_to_jsonlogic(&parsed).unwrap();
        // This demonstrates semantic but not exact roundtrip
        assert_eq!(back_to_json, r#"{"!":[{"==":[1,2]}]}"#);
        assert_ne!(back_to_json, original_json); // Not exact roundtrip
    }
}
