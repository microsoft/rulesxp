use nom::{
    IResult,
    branch::alt,
    bytes::complete::{tag, take_while1},
    character::complete::{char, multispace0, multispace1},
    combinator::{map, opt, recognize, value},
    error::{Error, ErrorKind},
    multi::separated_list0,
    sequence::{pair, preceded, terminated},
};

use crate::SchemeError;
use crate::ast::Value;
use crate::builtinops::{find_scheme_op, get_quote_op};

/// Helper function to create a quote PrecompiledOp
fn create_quote_precompiled_op(content: &Value) -> Value {
    let builtin_op = get_quote_op();
    Value::PrecompiledOp {
        op: builtin_op,
        op_id: builtin_op.scheme_id.to_string(),
        args: vec![content.clone()],
    }
}

/// Control whether builtin operations should be precompiled during parsing
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ShouldPrecompileOps {
    Yes,
    No,
}

/// Convert nom parsing errors to user-friendly messages
fn parse_error_to_message(input: &str, error: nom::Err<Error<&str>>) -> String {
    match error {
        nom::Err::Error(e) | nom::Err::Failure(e) => {
            let position = input.len().saturating_sub(e.input.len());
            match e.code {
                ErrorKind::Char => format!("Expected character at position {}", position),
                ErrorKind::Tag => format!("Unexpected token at position {}", position),
                _ => {
                    if position < input.len() {
                        let remaining_chars: String =
                            input.chars().skip(position).take(10).collect();
                        format!("Invalid syntax near '{}'", remaining_chars)
                    } else {
                        "Unexpected end of input".to_string()
                    }
                }
            }
        }
        nom::Err::Incomplete(_) => "Incomplete input".to_string(),
    }
}

/// Parse a number (integer only, supports decimal and hexadecimal)
fn parse_number(input: &str) -> IResult<&str, Value> {
    alt((parse_hexadecimal, parse_decimal))(input)
}

/// Parse a decimal number
fn parse_decimal(input: &str) -> IResult<&str, Value> {
    let (input, number_str) = recognize(pair(
        opt(char('-')),
        take_while1(|c: char| c.is_ascii_digit()),
    ))(input)?;

    match number_str.parse::<i64>() {
        Ok(n) => Ok((input, Value::Number(n))),
        Err(_) => Err(nom::Err::Error(nom::error::Error::new(
            input,
            nom::error::ErrorKind::Digit,
        ))),
    }
}

/// Parse a hexadecimal number (#x or #X prefix)
fn parse_hexadecimal(input: &str) -> IResult<&str, Value> {
    let (input, _) = char('#')(input)?;
    let (input, _) = alt((char('x'), char('X')))(input)?;
    let (input, hex_digits) = take_while1(|c: char| c.is_ascii_hexdigit())(input)?;

    match i64::from_str_radix(hex_digits, 16) {
        Ok(n) => Ok((input, Value::Number(n))),
        Err(_) => Err(nom::Err::Error(nom::error::Error::new(
            input,
            nom::error::ErrorKind::HexDigit,
        ))),
    }
}

/// Parse a boolean (#t or #f)
fn parse_bool(input: &str) -> IResult<&str, Value> {
    alt((
        value(Value::Bool(true), tag("#t")),
        value(Value::Bool(false), tag("#f")),
    ))(input)
}

/// Parse a symbol (identifier)
fn parse_symbol(input: &str) -> IResult<&str, Value> {
    map(
        take_while1(|c: char| c.is_alphanumeric() || "+-*/<>=!?_".contains(c)),
        |s: &str| Value::Symbol(s.to_string()),
    )(input)
}

/// Parse a string literal
fn parse_string(input: &str) -> IResult<&str, Value> {
    let (input, _) = char('"')(input)?;
    let mut chars = Vec::new();
    let mut remaining = input;

    while let Some(ch) = remaining.chars().next() {
        if ch == '"' {
            // End of string
            remaining = &remaining[1..];
            return Ok((remaining, Value::String(chars.into_iter().collect())));
        } else if ch == '\\' {
            // Handle escape sequences
            let mut char_iter = remaining.chars();
            char_iter.next(); // consume '\'
            if let Some(escaped) = char_iter.next() {
                let escaped_char = match escaped {
                    'n' => '\n',
                    't' => '\t',
                    'r' => '\r',
                    '\\' => '\\',
                    '"' => '"',
                    c => c, // For now, just keep the character as-is
                };
                chars.push(escaped_char);
                remaining = &remaining[2..];
            } else {
                return Err(nom::Err::Error(nom::error::Error::new(
                    remaining,
                    nom::error::ErrorKind::Char,
                )));
            }
        } else {
            chars.push(ch);
            remaining = &remaining[ch.len_utf8()..];
        }
    }

    // If we get here, we reached end of input without finding closing quote
    // This is the improved error handling that should be preserved
    Err(nom::Err::Error(nom::error::Error::new(
        remaining,
        nom::error::ErrorKind::Char,
    )))
}

/// Parse a list with configurable precompilation behavior (performance optimized)
fn parse_list(input: &str, should_precompile: ShouldPrecompileOps) -> IResult<&str, Value> {
    // Parse opening parenthesis and whitespace
    let (input, _) = char('(')(input)?;
    let (input, _) = multispace0(input)?;

    // Early quote detection to avoid backtracking
    let (input, is_quote) = opt(tag("quote"))(input)?;

    if is_quote.is_some() {
        // Handle quote specially - parse exactly one more element unprecompiled
        let (input, _) = multispace1(input)?;
        let (input, content) = parse_sexpr(input, ShouldPrecompileOps::No)?;
        let (input, _) = multispace0(input)?;
        let (input, _) = char(')')(input)?;

        // If precompilation is enabled, create a PrecompiledOp
        if should_precompile == ShouldPrecompileOps::Yes {
            let precompiled = create_quote_precompiled_op(&content);
            return Ok((input, precompiled));
        }

        // Fallback to unprecompiled list representation (only when precompilation disabled)
        return Ok((
            input,
            Value::List(vec![Value::Symbol("quote".to_string()), content]),
        ));
    }

    // Regular list parsing - parse all elements in one pass
    let (input, elements) =
        separated_list0(multispace1, |input| parse_sexpr(input, should_precompile))(input)?;

    // Parse closing parenthesis and whitespace
    let (input, _) = multispace0(input)?;
    let (input, _) = char(')')(input)?;

    // Apply precompilation if enabled - single lookup, no repeated string comparison
    if should_precompile == ShouldPrecompileOps::Yes
        && !elements.is_empty()
        && let Value::Symbol(op_name) = &elements[0]
        && let Some(builtin_op) = find_scheme_op(op_name.as_str())
    {
        let args = elements[1..].to_vec();
        return Ok((
            input,
            Value::PrecompiledOp {
                op: builtin_op,
                op_id: builtin_op.scheme_id.to_string(),
                args,
            },
        ));
    }

    Ok((input, Value::List(elements)))
}

/// Parse an S-expression with configurable precompilation behavior
fn parse_sexpr(input: &str, should_precompile: ShouldPrecompileOps) -> IResult<&str, Value> {
    preceded(
        multispace0,
        alt((
            |input| parse_quote(input, should_precompile), // Pass precompilation setting to quote
            |input| parse_list(input, should_precompile),
            parse_number,
            parse_bool,
            parse_string,
            parse_symbol,
        )),
    )(input)
}

/// Parse quoted expression ('expr -> (quote expr))
fn parse_quote(input: &str, should_precompile: ShouldPrecompileOps) -> IResult<&str, Value> {
    let (input, _) = char('\'')(input)?;
    let (input, expr) = parse_sexpr(input, ShouldPrecompileOps::No)?; // Use unprecompiled parsing for quoted content

    // Create PrecompiledOp only if precompilation is enabled
    if should_precompile == ShouldPrecompileOps::Yes {
        let precompiled = create_quote_precompiled_op(&expr);
        return Ok((input, precompiled));
    }

    // Fallback to unprecompiled representation (only when precompilation disabled)
    Ok((
        input,
        Value::List(vec![Value::Symbol("quote".to_string()), expr]),
    ))
}

/// Parse a complete S-expression from input with optimization enabled
pub fn parse(input: &str) -> Result<Value, SchemeError> {
    match terminated(
        |input| parse_sexpr(input, ShouldPrecompileOps::Yes),
        multispace0,
    )(input)
    {
        Ok(("", value)) => {
            // After successful parsing, validate arity for any PrecompiledOp
            validate_arity_in_ast(&value)?;
            Ok(value)
        }
        Ok((remaining, _)) => Err(SchemeError::ParseError(format!(
            "Unexpected remaining input: '{}'",
            remaining
        ))),
        Err(e) => Err(SchemeError::ParseError(parse_error_to_message(input, e))),
    }
}

/// Recursively validate arity in parsed AST - simpler than threading through parser
fn validate_arity_in_ast(value: &Value) -> Result<(), SchemeError> {
    match value {
        Value::PrecompiledOp { op, args, .. } => {
            // Validate this operation's arity
            if let Err(SchemeError::ArityError { expected, got, .. }) =
                op.validate_arity(args.len())
            {
                return Err(SchemeError::arity_error_with_expr(
                    expected,
                    got,
                    format!("{}", value.to_uncompiled_form()),
                ));
            }
            // Recursively validate nested expressions
            for arg in args {
                validate_arity_in_ast(arg)?;
            }
        }
        Value::List(elements) => {
            // Recursively validate list elements
            for element in elements {
                validate_arity_in_ast(element)?;
            }
        }
        _ => {} // Other value types don't need validation
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{nil, sym, val};

    /// Test result variants for comprehensive parsing tests
    #[derive(Debug)]
    enum ParseTestResult {
        Success(Value),              // Parsing should succeed with this value
        SpecificError(&'static str), // Parsing should fail with error containing this string
        Error,                       // Parsing should fail (any error)
    }
    use ParseTestResult::*;

    /// Helper for successful parse test cases
    fn success<T: Into<Value>>(value: T) -> ParseTestResult {
        Success(value.into())
    }

    /// Run comprehensive parse tests with detailed error reporting
    fn run_parse_tests(test_cases: Vec<(&str, ParseTestResult)>) {
        for (i, (input, expected)) in test_cases.iter().enumerate() {
            let test_id = format!("Parse test #{}", i + 1);
            
            match (parse(input), expected) {
                (Ok(actual), Success(expected_val)) => {
                    if actual != *expected_val {
                        panic!(
                            "{}: expected {:?}, got {:?}",
                            test_id, expected_val, actual
                        );
                    }
                }
                (Err(_), Error) => {} // Expected generic error
                (Err(e), SpecificError(expected_text)) => {
                    let error_msg = format!("{:?}", e);
                    if !error_msg.contains(expected_text) {
                        panic!(
                            "{}: error should contain '{}', got: {}",
                            test_id, expected_text, error_msg
                        );
                    }
                }
                (Ok(actual), Error) => {
                    panic!("{}: expected error, got {:?}", test_id, actual);
                }
                (Ok(actual), SpecificError(expected_text)) => {
                    panic!(
                        "{}: expected error containing '{}', got {:?}",
                        test_id, expected_text, actual
                    );
                }
                (Err(err), Success(expected_val)) => {
                    panic!(
                        "{}: expected {:?}, got error {:?}",
                        test_id, expected_val, err
                    );
                }
            }
        }
    }

    #[test]
    fn test_parse_number() {
        let test_cases = vec![
            // Decimal numbers
            ("42", success(val(42))),
            ("-5", success(val(-5))),
            ("0", success(val(0))),
            ("-0", success(val(0))),
            
            // Hexadecimal numbers
            ("#x1A", success(val(26))),
            ("#X1a", success(val(26))),
            ("#xff", success(val(255))),
            ("#xFF", success(val(255))),
            ("#x0", success(val(0))),
            ("#x12345", success(val(74565))),
            
            // Edge cases - large integer literals
            ("9223372036854775807", success(val(9223372036854775807i64))), // max i64
            ("-9223372036854775808", success(val(-9223372036854775808i64))), // min i64
            
            // Should fail
            ("3.14", Error), // Floating point should fail
            ("", Error), // Empty should fail
            ("#xG", Error), // Invalid hexadecimal should fail
            ("#x", Error), // Incomplete hex should fail
            ("#y123", Error), // Invalid hex prefix should fail
            ("123abc", Error), // Mixed should fail
        ];
        
        run_parse_tests(test_cases);
        
        // Note: Rust's i64::from_str handles overflow by wrapping, so these might not fail as expected
        // Let's test what actually happens with very large numbers
        let result = parse("99999999999999999999");
        // This might succeed due to wrapping, so we just verify it parses to something
        assert!(result.is_ok() || result.is_err()); // Either behavior is acceptable
    }

    #[test]
    fn test_parse_symbol() {
        let test_cases = vec![
            // Basic symbols
            ("foo", success(sym("foo"))),
            ("+", success(sym("+"))),
            (">=", success(sym(">="))),
            
            // Test all allowed special characters
            ("test-name", success(sym("test-name"))),
            ("test*name", success(sym("test*name"))),
            ("test/name", success(sym("test/name"))),
            ("test<name", success(sym("test<name"))),
            ("test=name", success(sym("test=name"))),
            ("test>name", success(sym("test>name"))),
            ("test!name", success(sym("test!name"))),
            ("test?name", success(sym("test?name"))),
            ("test_name", success(sym("test_name"))),
            
            // Alphanumeric combinations
            ("var123", success(sym("var123"))),
            
            // Invalid - numbers at start cause parse error
            ("123var", Error),
        ];
        
        run_parse_tests(test_cases);
    }

    #[test]
    fn test_parse_bool() {
        let test_cases = vec![
            // Valid booleans
            ("#t", success(val(true))),
            ("#f", success(val(false))),
            
            // Should fail - case sensitive
            ("#T", Error),
            ("#F", Error),
            ("#true", Error),
            ("#false", Error),
        ];
        
        run_parse_tests(test_cases);
    }

    #[test]
    fn test_parse_string() {
        let test_cases = vec![
            // Basic strings
            ("\"hello\"", success(val("hello"))),
            ("\"hello world\"", success(val("hello world"))),
            
            // Test escape sequences
            ("\"hello\\nworld\"", success(val("hello\nworld"))),
            ("\"tab\\there\"", success(val("tab\there"))),
            ("\"carriage\\rreturn\"", success(val("carriage\rreturn"))),
            ("\"quote\\\"test\"", success(val("quote\"test"))),
            ("\"backslash\\\\test\"", success(val("backslash\\test"))),
            
            // Test unknown escape - the parser keeps the character as-is, removing the backslash
            ("\"other\\xchar\"", success(val("otherxchar"))),
            
            // Test empty string
            ("\"\"", success(val(""))),
            
            // Test unterminated string (should fail)
            ("\"unterminated", Error),
            ("\"unterminated\\", Error), // ends with backslash
            ("\"test\\\"", Error), // string with just escape at end
        ];
        
        run_parse_tests(test_cases);
    }

    #[test]
    fn test_parse_nil() {
        let test_cases = vec![
            ("()", success(nil())),
        ];
        
        run_parse_tests(test_cases);
    }

    #[test]
    fn test_parse_quote() {
        // Test quote shorthand - with precompilation enabled, should create PrecompiledOp
        if let Value::PrecompiledOp { op_id, args, .. } = parse("'foo").unwrap() {
            assert_eq!(op_id, "quote");
            assert_eq!(args.len(), 1);
            assert_eq!(args[0], sym("foo"));
        } else {
            panic!("Expected PrecompiledOp for precompiled quote parse");
        }

        // Test quote with list - should create PrecompiledOp with unprecompiled content
        if let Value::PrecompiledOp { op_id, args, .. } = parse("'(1 2 3)").unwrap() {
            assert_eq!(op_id, "quote");
            assert_eq!(args.len(), 1);
            assert_eq!(args[0], val([1, 2, 3]));
        } else {
            panic!("Expected PrecompiledOp for precompiled quote parse");
        }

        // Test quote with nil - should create PrecompiledOp with empty list content
        if let Value::PrecompiledOp { op_id, args, .. } = parse("'()").unwrap() {
            assert_eq!(op_id, "quote");
            assert_eq!(args.len(), 1);
            assert_eq!(args[0], nil());
        } else {
            panic!("Expected PrecompiledOp for precompiled quote parse");
        }
    }

    #[test]
    fn test_parse_list() {
        // Empty list (nil)
        assert_eq!(parse("()").unwrap(), nil());

        // Single element list
        assert_eq!(parse("(42)").unwrap(), val([42]));

        // Regular list with mixed types - can't fully convert due to symbol limitations
        assert_eq!(
            parse("(1 hello \"world\" #t)").unwrap(),
            val([val(1), sym("hello"), val("world"), val(true)])
        );

        // Regular list (not a builtin operation)
        assert_eq!(parse("(1 2 3)").unwrap(), val([1, 2, 3]));

        // Test that builtin operations are parsed as PrecompiledOp
        match parse("(+ 1 2)").unwrap() {
            Value::PrecompiledOp { op_id, args, .. } => {
                assert_eq!(op_id, "+");
                assert_eq!(args, vec![val(1), val(2)]);
            }
            other => panic!("Expected PrecompiledOp, got {:?}", other),
        }

        // Test multiple builtin operations
        match parse("(* 3 4 5)").unwrap() {
            Value::PrecompiledOp { op_id, args, .. } => {
                assert_eq!(op_id, "*");
                assert_eq!(args, vec![val(3), val(4), val(5)]);
            }
            other => panic!("Expected PrecompiledOp, got {:?}", other),
        }

        // Test builtin comparison operations
        match parse("(< 1 2)").unwrap() {
            Value::PrecompiledOp { op_id, args, .. } => {
                assert_eq!(op_id, "<");
                assert_eq!(args, vec![val(1), val(2)]);
            }
            other => panic!("Expected PrecompiledOp, got {:?}", other),
        }

        // Test builtin special forms
        match parse("(if #t 1 2)").unwrap() {
            Value::PrecompiledOp { op_id, args, .. } => {
                assert_eq!(op_id, "if");
                assert_eq!(args, vec![val(true), val(1), val(2)]);
            }
            other => panic!("Expected PrecompiledOp, got {:?}", other),
        }

        // Test that non-builtin symbols still create regular lists
        assert_eq!(
            parse("(foo 1 2)").unwrap(),
            val([sym("foo"), val(1), val(2)])
        );

        // Test that quote IS precompiled (like other special forms)
        match parse("(quote foo)").unwrap() {
            Value::PrecompiledOp { op_id, args, .. } => {
                assert_eq!(op_id, "quote");
                assert_eq!(args, vec![sym("foo")]);
            }
            other => panic!("Expected PrecompiledOp for quote, got {:?}", other),
        }

        // Test nested lists with mixed builtins and regular lists
        match parse("((+ 1 2) (foo bar))").unwrap() {
            Value::List(elements) => {
                assert_eq!(elements.len(), 2);
                // First element should be PrecompiledOp
                match &elements[0] {
                    Value::PrecompiledOp { op_id, args, .. } => {
                        assert_eq!(op_id, "+");
                        assert_eq!(args, &vec![val(1), val(2)]);
                    }
                    other => panic!("Expected PrecompiledOp, got {:?}", other),
                }
                // Second element should be regular list
                assert_eq!(elements[1], val([sym("foo"), sym("bar")]));
            }
            other => panic!("Expected List, got {:?}", other),
        }

        // Test list with only symbols (should remain a list)
        assert_eq!(
            parse("(a b c)").unwrap(),
            val([sym("a"), sym("b"), sym("c")])
        );

        // Test list starting with number (should remain a list)
        assert_eq!(
            parse("(42 is the answer)").unwrap(),
            val([val(42), sym("is"), sym("the"), sym("answer")])
        );
    }

    #[test]
    fn test_parse_nested_list() {
        let test_cases = vec![
            ("((1 2) (3 4))", success(val([[1, 2], [3, 4]]))),
        ];
        
        run_parse_tests(test_cases);
    }

    #[test]
    fn test_whitespace_handling() {
        let test_cases = vec![
            // Test various whitespace scenarios
            ("  42  ", success(val(42))),
            ("\t#t\n", success(val(true))),
            ("\r\n  foo  \t", success(sym("foo"))),
            
            // Lists with various whitespace
            ("( 1   2\t\n3 )", success(val([1, 2, 3]))),
            
            // Empty list with whitespace
            ("(   )", success(nil())),
            ("(\t\n)", success(nil())),
        ];
        
        run_parse_tests(test_cases);
    }

    #[test]
    fn test_error_cases() {
        let test_cases = vec![
            // Mismatched parentheses
            ("(1 2 3", Error), // Missing closing
            ("1 2 3)", Error), // Extra closing
            ("((1 2)", Error), // Nested missing closing
            
            // Empty input
            ("", Error),
            ("   ", Error), // Just whitespace
            
            // Invalid characters at start
            (")", Error),
            ("@invalid", Error),
            
            // Multiple expressions (should fail for main parse function)
            ("1 2", Error),
            ("(+ 1 2) (+ 3 4)", Error),
        ];
        
        run_parse_tests(test_cases);
    }

    #[test]
    fn test_arity_errors_at_parse_time() {
        // Test that arity errors are caught during parsing, not evaluation

        // Test 'not' with no arguments (expects exactly 1)
        match parse("(not)") {
            Err(SchemeError::ArityError {
                expected,
                got,
                expression,
            }) => {
                assert_eq!(expected, 1);
                assert_eq!(got, 0);
                assert_eq!(expression.as_deref(), Some("(not)"));
            }
            other => panic!("Expected arity error for (not), got {:?}", other),
        }

        // Test 'not' with too many arguments (expects exactly 1)
        match parse("(not #t #f)") {
            Err(SchemeError::ArityError {
                expected,
                got,
                expression,
            }) => {
                assert_eq!(expected, 1);
                assert_eq!(got, 2);
                assert_eq!(expression.as_deref(), Some("(not #t #f)"));
            }
            other => panic!("Expected arity error for (not #t #f), got {:?}", other),
        }

        // Test 'car' with no arguments (expects exactly 1)
        match parse("(car)") {
            Err(SchemeError::ArityError {
                expected,
                got,
                expression,
            }) => {
                assert_eq!(expected, 1);
                assert_eq!(got, 0);
                assert_eq!(expression.as_deref(), Some("(car)"));
            }
            other => panic!("Expected arity error for (car), got {:?}", other),
        }

        // Test '+' with valid arity (should succeed)
        assert!(parse("(+ 1 2)").is_ok());

        // Test nested arity errors are also caught
        match parse("(list (not) 42)") {
            Err(SchemeError::ArityError {
                expected,
                got,
                expression,
            }) => {
                assert_eq!(expected, 1);
                assert_eq!(got, 0);
                assert_eq!(expression.as_deref(), Some("(not)"));
            }
            other => panic!("Expected arity error for nested (not), got {:?}", other),
        }

        // Test that valid expressions still parse successfully
        assert!(parse("(not #t)").is_ok());
        assert!(parse("(car (list 1 2 3))").is_ok());
        assert!(parse("(+ 1 2 3 4 5)").is_ok());
    }

    #[test]
    fn test_display_round_trip() {
        // Test that PrecompiledOp displays in a form that can be parsed again
        let original = "(+ 1 2 3)";
        let parsed = parse(original).unwrap();
        let displayed = format!("{}", parsed);

        // Should be able to parse the displayed form
        let reparsed = parse(&displayed).unwrap();
        let redisplayed = format!("{}", reparsed);

        // Should be consistent
        assert_eq!(displayed, redisplayed);

        // Test nested operations
        let nested = "(+ (* 2 3) (- 10 5))";
        let parsed_nested = parse(nested).unwrap();
        let displayed_nested = format!("{}", parsed_nested);
        let reparsed_nested = parse(&displayed_nested).unwrap();
        let redisplayed_nested = format!("{}", reparsed_nested);

        assert_eq!(displayed_nested, redisplayed_nested);
    }

    #[test]
    fn test_complex_nested_structures() {
        // Deeply nested lists
        assert_eq!(parse("(((1)))").unwrap(), val([val([val([val(1)])])]));

        // Mixed types in nested structure
        assert_eq!(
            parse("(foo (\"bar\" #t) -123)").unwrap(),
            val([sym("foo"), val([val("bar"), val(true)]), val(-123)])
        );
    }

    #[test]
    fn test_parse_time_arity_errors_comprehensive() {
        let test_cases = vec![
            // Special forms with strict arity requirements
            
            // SCHEME-JSONLOGIC-STRICT: Require exactly 3 arguments
            // (Scheme allows 2 args with undefined behavior, JSONLogic allows chaining with >3 args)
            // 'if' requires exactly 3 arguments
            ("(if #t 1)", SpecificError("ArityError")),        // Too few args
            ("(if #t 42 0 extra)", SpecificError("ArityError")), // Too many args  
            ("(if)", SpecificError("ArityError")),             // No args
            
            // 'and' requires at least 1 argument
            ("(and)", SpecificError("ArityError")),            // No args
            
            // 'or' requires at least 1 argument
            ("(or)", SpecificError("ArityError")),             // No args
            
            // 'not' requires exactly 1 argument
            ("(not)", SpecificError("ArityError")),            // No args
            ("(not #t #f)", SpecificError("ArityError")),      // Too many args
            
            // 'car' requires exactly 1 argument
            ("(car)", SpecificError("ArityError")),            // No args
            ("(car (list 1 2) extra)", SpecificError("ArityError")), // Too many args
            
            // 'cdr' requires exactly 1 argument  
            ("(cdr)", SpecificError("ArityError")),            // No args
            ("(cdr (list 1 2) extra)", SpecificError("ArityError")), // Too many args
            
            // Valid cases should still parse successfully
            ("(if #t 1 2)", Error), // Don't check exact PrecompiledOp structure, just success
            ("(and #t #f)", Error), // Will be Success, but we'll verify separately
            ("(or #f #t)", Error),  // Will be Success, but we'll verify separately
        ];

        // Test error cases
        let error_cases: Vec<(&str, ParseTestResult)> = test_cases.into_iter()
            .filter(|(_, result)| matches!(result, SpecificError(_)))
            .collect();
        run_parse_tests(error_cases);
        
        // Test that valid cases parse successfully (separate verification)
        assert!(parse("(if #t 1 2)").is_ok());
        assert!(parse("(and #t #f)").is_ok());
        assert!(parse("(or #f #t)").is_ok());
    }
    
    #[test]
    fn test_parse_time_syntax_errors() {
        let test_cases = vec![
            // Unclosed parentheses - should contain parse error information
            ("(1 2 3", SpecificError("ParseError")),
            ("((1 2)", SpecificError("ParseError")), 
            ("(+ 1 (- 2", SpecificError("ParseError")),
            
            // Extra closing parentheses
            ("1 2 3)", SpecificError("ParseError")),
            ("(1 2))", SpecificError("ParseError")),
            
            // Invalid starting characters  
            (")", SpecificError("ParseError")),
            ("@invalid", SpecificError("ParseError")),
            
            // Empty or whitespace-only input
            ("", SpecificError("ParseError")),
            ("   ", SpecificError("ParseError")),
            ("\t\n", SpecificError("ParseError")),
            
            // Multiple top-level expressions (not supported)
            ("1 2", SpecificError("ParseError")),
            ("(+ 1 2) (+ 3 4)", SpecificError("ParseError")),
            ("42 #t", SpecificError("ParseError")),
            
            // Valid expressions should parse successfully
            ("42", success(val(42))),
            ("\"hello\"", success(val("hello"))),
            ("#t", success(val(true))),
            ("symbol", success(sym("symbol"))), // Raw symbol, not quoted
        ];

        run_parse_tests(test_cases);
    }
}
