use crate::SchemeError;
use crate::ast::Value;
use crate::builtinops::{map_jsonlogic_id_to_scheme, map_scheme_id_to_jsonlogic};
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
    // Helper function to normalize operands for unary operations
    // JSONLogic allows {"!": true} as sugar for {"!": [true]}
    let normalize_unary_operands =
        |op_name: &str, operands: serde_json::Value| -> Result<Value, SchemeError> {
            let converted = convert_json_to_value(operands)?;
            match converted {
                // If it's a list with exactly one element, return that element
                Value::List(list) => match list.as_slice() {
                    [single_element] => Ok(single_element.clone()),
                    _ => Err(SchemeError::ParseError(format!(
                        "{} operation requires exactly 1 argument, got {} arguments: {:?}",
                        op_name,
                        list.len(),
                        list
                    ))),
                },
                // If it's a single value, return it directly
                single_value => Ok(single_value),
            }
        };

    // Helper function to validate and extract operands for binary operations
    let extract_binary_operands =
        |op_name: &str, operands: serde_json::Value| -> Result<(Value, Value), SchemeError> {
            let converted = convert_json_to_value(operands)?;
            match converted {
                Value::List(list) => match list.as_slice() {
                    [first, second] => Ok((first.clone(), second.clone())),
                    _ => Err(SchemeError::ParseError(format!(
                        "{} operation requires exactly 2 arguments, got {} arguments: {:?}",
                        op_name,
                        list.len(),
                        list
                    ))),
                },
                _ => Err(SchemeError::ParseError(format!(
                    "{} operands must be an array",
                    op_name
                ))),
            }
        };

    // Helper function to extract operands for operations that take one or more arguments
    let extract_operand_list =
        |op_name: &str, operands: serde_json::Value| -> Result<Vec<Value>, SchemeError> {
            let converted = convert_json_to_value(operands)?;
            match converted {
                Value::List(list) => {
                    if list.is_empty() {
                        Err(SchemeError::ParseError(format!(
                            "{} operation requires at least 1 argument, got 0 arguments",
                            op_name
                        )))
                    } else {
                        Ok(list)
                    }
                }
                // If it's a single value, wrap it in a list
                single_value => Ok(vec![single_value]),
            }
        };

    match operator {
        // Logical operators
        "and" => {
            let args = extract_operand_list("and", operands)?;
            Ok(Value::List(
                [Value::Symbol("and".to_string())]
                    .into_iter()
                    .chain(args)
                    .collect(),
            ))
        }
        "or" => {
            let args = extract_operand_list("or", operands)?;
            Ok(Value::List(
                [Value::Symbol("or".to_string())]
                    .into_iter()
                    .chain(args)
                    .collect(),
            ))
        }
        "!" => {
            let arg = normalize_unary_operands("!", operands)?;
            Ok(Value::List(vec![
                Value::Symbol(map_jsonlogic_id_to_scheme("!").to_string()),
                arg,
            ]))
        }

        // Comparison operators
        "==" => {
            let (first, second) = extract_binary_operands("==", operands)?;
            Ok(Value::List(vec![
                Value::Symbol(map_jsonlogic_id_to_scheme("==").to_string()),
                first,
                second,
            ]))
        }
        "!=" => {
            let (first, second) = extract_binary_operands("!=", operands)?;
            Ok(Value::List(vec![
                Value::Symbol("not".to_string()),
                Value::List(vec![
                    Value::Symbol(map_jsonlogic_id_to_scheme("==").to_string()),
                    first,
                    second,
                ]),
            ]))
        }
        ">" => {
            let (first, second) = extract_binary_operands(">", operands)?;
            Ok(Value::List(vec![
                Value::Symbol(">".to_string()),
                first,
                second,
            ]))
        }
        ">=" => {
            let (first, second) = extract_binary_operands(">=", operands)?;
            Ok(Value::List(vec![
                Value::Symbol(">=".to_string()),
                first,
                second,
            ]))
        }
        "<" => {
            let (first, second) = extract_binary_operands("<", operands)?;
            Ok(Value::List(vec![
                Value::Symbol("<".to_string()),
                first,
                second,
            ]))
        }
        "<=" => {
            let (first, second) = extract_binary_operands("<=", operands)?;
            Ok(Value::List(vec![
                Value::Symbol("<=".to_string()),
                first,
                second,
            ]))
        }

        // Arithmetic operators
        "+" => {
            let args = extract_operand_list("+", operands)?;
            Ok(Value::List(
                [Value::Symbol("+".to_string())]
                    .into_iter()
                    .chain(args)
                    .collect(),
            ))
        }
        "-" => {
            let args = extract_operand_list("-", operands)?;
            Ok(Value::List(
                [Value::Symbol("-".to_string())]
                    .into_iter()
                    .chain(args)
                    .collect(),
            ))
        }
        "*" => {
            let args = extract_operand_list("*", operands)?;
            Ok(Value::List(
                [Value::Symbol("*".to_string())]
                    .into_iter()
                    .chain(args)
                    .collect(),
            ))
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

        // Conditional
        "if" => {
            let args = convert_json_to_value(operands)?;
            if let Value::List(list) = args {
                if list.len() < 2 || list.len() > 3 {
                    return Err(SchemeError::ParseError(
                        "if requires 2 or 3 arguments".to_string(),
                    ));
                }
                Ok(Value::List(vec![
                    Value::Symbol("if".to_string()),
                    list[0].clone(),
                    list[1].clone(),
                    list.get(2).cloned().unwrap_or(Value::List(vec![])), // default else is nil
                ]))
            } else {
                Err(SchemeError::ParseError(
                    "if operands must be an array".to_string(),
                ))
            }
        }

        _ => Err(SchemeError::ParseError(format!(
            "Unknown JSONLogic operator: {}",
            operator
        ))),
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
        Value::PrecompiledOp { .. } => Err(SchemeError::EvalError(
            "Cannot convert precompiled operation to JSONLogic".to_string(),
        )),
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
            result,
            Value::List(vec![
                Value::Symbol("and".to_string()),
                Value::Bool(true),
                Value::Bool(false)
            ])
        );

        // {"or": [true, false]}
        let result = parse_jsonlogic(r#"{"or": [true, false]}"#).unwrap();
        assert_eq!(
            result,
            Value::List(vec![
                Value::Symbol("or".to_string()),
                Value::Bool(true),
                Value::Bool(false)
            ])
        );

        // {"!": [true]}
        let result = parse_jsonlogic(r#"{"!": [true]}"#).unwrap();
        assert_eq!(
            result,
            Value::List(vec![Value::Symbol("not".to_string()), Value::Bool(true)])
        );
    }

    #[test]
    fn test_parse_comparisons() {
        // {"==": [1, 1]}
        let result = parse_jsonlogic(r#"{"==": [1, 1]}"#).unwrap();
        assert_eq!(
            result,
            Value::List(vec![
                Value::Symbol("equal?".to_string()),
                Value::Number(1),
                Value::Number(1)
            ])
        );

        // {">": [2, 1]}
        let result = parse_jsonlogic(r#"{">": [2, 1]}"#).unwrap();
        assert_eq!(
            result,
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
            result,
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
            result,
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
    fn test_error_cases() {
        // Invalid JSON
        assert!(parse_jsonlogic("invalid json").is_err());

        // Multiple keys in object
        assert!(parse_jsonlogic(r#"{"and": true, "or": false}"#).is_err());

        // Unknown operator
        assert!(parse_jsonlogic(r#"{"unknown": [1, 2]}"#).is_err());
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
}
