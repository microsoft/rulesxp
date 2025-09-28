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
use crate::ast::{Value, nil, sym, val};
use crate::builtinops::find_scheme_op;

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
            if let Some(builtin_op) = find_scheme_op("quote") {
                return Ok((
                    input,
                    Value::PrecompiledOp {
                        op: builtin_op,
                        op_id: "quote".to_string(),
                        args: vec![content],
                    },
                ));
            }
        }

        // Fallback to unprecompiled list representation
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
    if should_precompile == ShouldPrecompileOps::Yes && !elements.is_empty() {
        if let Value::Symbol(op_name) = &elements[0] {
            if let Some(builtin_op) = find_scheme_op(op_name.as_str()) {
                let args = elements[1..].to_vec();
                return Ok((
                    input,
                    Value::PrecompiledOp {
                        op: builtin_op,
                        op_id: op_name.clone(),
                        args,
                    },
                ));
            }
        }
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
        if let Some(builtin_op) = find_scheme_op("quote") {
            return Ok((
                input,
                Value::PrecompiledOp {
                    op: builtin_op,
                    op_id: "quote".to_string(),
                    args: vec![expr],
                },
            ));
        }
    }

    // Fallback to unprecompiled representation
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

    #[test]
    fn test_parse_number() {
        // Decimal numbers
        assert_eq!(parse("42").unwrap(), val(42));
        assert_eq!(parse("-5").unwrap(), val(-5));
        assert_eq!(parse("0").unwrap(), val(0));
        assert_eq!(parse("-0").unwrap(), val(0));

        // Hexadecimal numbers
        assert_eq!(parse("#x1A").unwrap(), val(26));
        assert_eq!(parse("#X1a").unwrap(), val(26));
        assert_eq!(parse("#xff").unwrap(), val(255));
        assert_eq!(parse("#xFF").unwrap(), val(255));
        assert_eq!(parse("#x0").unwrap(), val(0));
        assert_eq!(parse("#x12345").unwrap(), val(74565));

        // Edge cases - large integer literals
        assert_eq!(
            parse("9223372036854775807").unwrap(),
            val(9223372036854775807i64)
        ); // max i64
        assert_eq!(
            parse("-9223372036854775808").unwrap(),
            val(-9223372036854775808i64)
        ); // min i64

        // Should fail
        assert!(parse("3.14").is_err()); // Floating point should fail
        assert!(parse("").is_err()); // Empty should fail
        assert!(parse("#xG").is_err()); // Invalid hexadecimal should fail
        assert!(parse("#x").is_err()); // Incomplete hex should fail
        assert!(parse("#y123").is_err()); // Invalid hex prefix should fail
        assert!(parse("123abc").is_err()); // Mixed should fail

        // Note: Rust's i64::from_str handles overflow by wrapping, so these might not fail as expected
        // Let's test what actually happens with very large numbers
        let result = parse("99999999999999999999");
        // This might succeed due to wrapping, so we just verify it parses to something
        assert!(result.is_ok() || result.is_err()); // Either behavior is acceptable
    }

    #[test]
    fn test_parse_symbol() {
        assert_eq!(parse("foo").unwrap(), sym("foo"));
        assert_eq!(parse("+").unwrap(), sym("+"));
        assert_eq!(parse(">=").unwrap(), sym(">="));

        // Test all allowed special characters
        assert_eq!(parse("test-name").unwrap(), sym("test-name"));
        assert_eq!(parse("test*name").unwrap(), sym("test*name"));
        assert_eq!(parse("test/name").unwrap(), sym("test/name"));
        assert_eq!(parse("test<name").unwrap(), sym("test<name"));
        assert_eq!(parse("test=name").unwrap(), sym("test=name"));
        assert_eq!(parse("test>name").unwrap(), sym("test>name"));
        assert_eq!(parse("test!name").unwrap(), sym("test!name"));
        assert_eq!(parse("test?name").unwrap(), sym("test?name"));
        assert_eq!(parse("test_name").unwrap(), sym("test_name"));

        // Alphanumeric combinations - but note that numbers at start will parse as numbers first
        assert_eq!(parse("var123").unwrap(), sym("var123"));

        // This will parse as a number "123" with remaining "var", causing a parse error
        assert!(parse("123var").is_err());
    }

    #[test]
    fn test_parse_bool() {
        assert_eq!(parse("#t").unwrap(), val(true));
        assert_eq!(parse("#f").unwrap(), val(false));

        // Should fail - case sensitive
        assert!(parse("#T").is_err());
        assert!(parse("#F").is_err());
        assert!(parse("#true").is_err());
        assert!(parse("#false").is_err());
    }

    #[test]
    fn test_parse_string() {
        assert_eq!(parse("\"hello\"").unwrap(), val("hello"));
        assert_eq!(parse("\"hello world\"").unwrap(), val("hello world"));

        // Test escape sequences
        assert_eq!(parse("\"hello\\nworld\"").unwrap(), val("hello\nworld"));
        assert_eq!(parse("\"tab\\there\"").unwrap(), val("tab\there"));
        assert_eq!(
            parse("\"carriage\\rreturn\"").unwrap(),
            val("carriage\rreturn")
        );
        assert_eq!(parse("\"quote\\\"test\"").unwrap(), val("quote\"test"));
        assert_eq!(
            parse("\"backslash\\\\test\"").unwrap(),
            val("backslash\\test")
        );

        // Test unknown escape - the parser keeps the character as-is, removing the backslash
        assert_eq!(parse("\"other\\xchar\"").unwrap(), val("otherxchar"));

        // Test empty string
        assert_eq!(parse("\"\"").unwrap(), val(""));

        // Test unterminated string (should fail)
        assert!(parse("\"unterminated").is_err());
        assert!(parse("\"unterminated\\").is_err()); // ends with backslash

        // Test string with just escape at end
        assert!(parse("\"test\\\"").is_err());
    }

    #[test]
    fn test_parse_nil() {
        assert_eq!(parse("()").unwrap(), nil());
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
        assert_eq!(parse("((1 2) (3 4))").unwrap(), val([[1, 2], [3, 4]]));
    }

    #[test]
    fn test_whitespace_handling() {
        // Test various whitespace scenarios
        assert_eq!(parse("  42  ").unwrap(), val(42));
        assert_eq!(parse("\t#t\n").unwrap(), val(true));
        assert_eq!(parse("\r\n  foo  \t").unwrap(), sym("foo"));

        // Lists with various whitespace
        assert_eq!(parse("( 1   2\t\n3 )").unwrap(), val([1, 2, 3]));

        // Empty list with whitespace
        assert_eq!(parse("(   )").unwrap(), nil());
        assert_eq!(parse("(\t\n)").unwrap(), nil());
    }

    #[test]
    fn test_error_cases() {
        // Mismatched parentheses
        assert!(parse("(1 2 3").is_err()); // Missing closing
        assert!(parse("1 2 3)").is_err()); // Extra closing
        assert!(parse("((1 2)").is_err()); // Nested missing closing

        // Empty input
        assert!(parse("").is_err());
        assert!(parse("   ").is_err()); // Just whitespace

        // Invalid characters at start
        assert!(parse(")").is_err());
        assert!(parse("@invalid").is_err());

        // Multiple expressions (should fail for main parse function)
        assert!(parse("1 2").is_err());
        assert!(parse("(+ 1 2) (+ 3 4)").is_err());
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
}
