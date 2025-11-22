use nom::{
    IResult, Parser,
    branch::alt,
    bytes::complete::{tag, take_while1},
    character::complete::{char, multispace0, multispace1},
    combinator::{opt, recognize, value},
    error::ErrorKind,
    multi::separated_list0,
    sequence::{pair, preceded, terminated},
};

use crate::Error;
use crate::MAX_PARSE_DEPTH;
use crate::ast::{NumberType, SYMBOL_SPECIAL_CHARS, Value, is_valid_symbol};
use crate::builtinops::{find_scheme_op, get_quote_op};

/// Helper function to create a quote PrecompiledOp
fn create_quote_precompiled_op(content: &Value) -> Value {
    let builtin_op = get_quote_op();
    Value::PrecompiledOp {
        op: builtin_op,
        op_id: builtin_op.scheme_id.into(),
        args: vec![content.clone()],
    }
}

/// Control whether builtin operations should be precompiled during parsing
#[derive(Debug, Clone, Copy, PartialEq)]
enum ShouldPrecompileOps {
    Yes,
    No,
}

/// Convert nom parsing errors to user-friendly messages
fn parse_error_to_message(input: &str, error: nom::Err<nom::error::Error<&str>>) -> String {
    match error {
        nom::Err::Error(e) | nom::Err::Failure(e) => {
            let position = input.len().saturating_sub(e.input.len());
            match e.code {
                ErrorKind::Char => format!("Expected character at position {position}"),
                ErrorKind::Tag => format!("Unexpected token at position {position}"),
                ErrorKind::TooLarge => {
                    format!("Expression too deeply nested (max depth: {MAX_PARSE_DEPTH})")
                }
                _ => {
                    if position < input.len() {
                        let remaining_chars: String =
                            input.chars().skip(position).take(10).collect();
                        format!("Invalid syntax near '{remaining_chars}'")
                    } else {
                        "Unexpected end of input".into()
                    }
                }
            }
        }
        nom::Err::Incomplete(_) => "Incomplete input".into(),
    }
}

/// Parse a number (integer only, supports decimal and hexadecimal)
fn parse_number(input: &str) -> IResult<&str, Value> {
    alt((parse_hexadecimal, parse_decimal)).parse(input)
}

/// Parse a decimal number
fn parse_decimal(input: &str) -> IResult<&str, Value> {
    let (input, number_str) = recognize(pair(
        opt(char('-')),
        take_while1(|c: char| c.is_ascii_digit()),
    ))
    .parse(input)?;

    match number_str.parse::<NumberType>() {
        Ok(n) => Ok((input, Value::Number(n))),
        Err(_) => {
            // Parse failed - could be due to overflow or invalid format
            // Symbol parsing will reject this anyway since it starts with digits
            Err(nom::Err::Error(nom::error::Error::new(
                input,
                nom::error::ErrorKind::Digit,
            )))
        }
    }
}

/// Parse a hexadecimal number (#x or #X prefix)
fn parse_hexadecimal(input: &str) -> IResult<&str, Value> {
    let (input, _) = char('#').parse(input)?;
    let (input, _) = alt((char('x'), char('X'))).parse(input)?;
    let (input, hex_digits) = take_while1(|c: char| c.is_ascii_hexdigit()).parse(input)?;

    match NumberType::from_str_radix(hex_digits, 16) {
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
    ))
    .parse(input)
}

/// Parse a symbol (identifier)
fn parse_symbol(input: &str) -> IResult<&str, Value> {
    let mut symbol_chars =
        take_while1(|c: char| c.is_alphanumeric() || SYMBOL_SPECIAL_CHARS.contains(c));

    let (remaining, candidate) = symbol_chars.parse(input)?;

    if is_valid_symbol(candidate) {
        Ok((remaining, Value::Symbol(candidate.into())))
    } else {
        Err(nom::Err::Error(nom::error::Error::new(
            input,
            nom::error::ErrorKind::Alpha,
        )))
    }
}

/// Parse a string literal
fn parse_string(input: &str) -> IResult<&str, Value> {
    let (mut remaining, _) = char('"').parse(input)?;
    let mut chars = Vec::new();

    loop {
        let mut char_iter = remaining.chars();
        match char_iter.next() {
            Some('"') => {
                // End of string - remaining is what's left after consuming the quote
                return Ok((
                    char_iter.as_str(),
                    Value::String(chars.into_iter().collect()),
                ));
            }
            Some('\\') => {
                // Handle escape sequences
                match char_iter.next() {
                    Some('n') => chars.push('\n'),
                    Some('t') => chars.push('\t'),
                    Some('r') => chars.push('\r'),
                    Some('\\') => chars.push('\\'),
                    Some('"') => chars.push('"'),
                    Some(_) => {
                        // Unknown escape sequence - return error
                        return Err(nom::Err::Error(nom::error::Error::new(
                            remaining,
                            nom::error::ErrorKind::Char,
                        )));
                    }
                    None => {
                        // Incomplete escape sequence (backslash at end)
                        return Err(nom::Err::Error(nom::error::Error::new(
                            remaining,
                            nom::error::ErrorKind::Char,
                        )));
                    }
                }
                // After consuming escape sequence, remaining is what the iterator has left
                remaining = char_iter.as_str();
            }
            Some(ch) => {
                // Regular character
                chars.push(ch);
                remaining = char_iter.as_str();
            }
            None => {
                // Reached end of input without finding closing quote
                return Err(nom::Err::Error(nom::error::Error::new(
                    remaining,
                    nom::error::ErrorKind::Char,
                )));
            }
        }
    }
}

/// Parse a list with configurable precompilation behavior (performance optimized)
fn parse_list(
    input: &str,
    should_precompile: ShouldPrecompileOps,
    depth: usize,
) -> IResult<&str, Value> {
    // Parse opening parenthesis and whitespace
    let (input, _) = char('(').parse(input)?;
    let (input, _) = multispace0.parse(input)?;

    // Early quote detection to avoid backtracking
    let (input, is_quote) = opt(tag("quote")).parse(input)?;

    if is_quote.is_some() {
        // Handle quote specially - parse exactly one more element unprecompiled
        let (input, _) = multispace1.parse(input)?;
        let (input, content) = parse_sexpr(input, ShouldPrecompileOps::No, depth + 1)?;
        let (input, _) = multispace0.parse(input)?;
        let (input, _) = char(')').parse(input)?;

        // If precompilation is enabled, create a PrecompiledOp
        if should_precompile == ShouldPrecompileOps::Yes {
            let precompiled = create_quote_precompiled_op(&content);
            return Ok((input, precompiled));
        }

        // Fallback to unprecompiled list representation (only when precompilation disabled)
        return Ok((
            input,
            Value::List(vec![Value::Symbol("quote".into()), content]),
        ));
    }

    // Regular list parsing - parse all elements in one pass
    let (input, elements) = separated_list0(multispace1, |input| {
        parse_sexpr(input, should_precompile, depth + 1)
    })
    .parse(input)?;

    // Parse closing parenthesis and whitespace
    let (input, _) = multispace0.parse(input)?;
    let (input, _) = char(')').parse(input)?;

    // Apply precompilation if enabled - single lookup, no repeated string comparison
    if should_precompile == ShouldPrecompileOps::Yes
        && let [Value::Symbol(op_name), args @ ..] = elements.as_slice()
        && let Some(builtin_op) = find_scheme_op(op_name.as_str())
    {
        return Ok((
            input,
            Value::PrecompiledOp {
                op: builtin_op,
                op_id: builtin_op.scheme_id.into(),
                args: args.to_vec(),
            },
        ));
    }

    Ok((input, Value::List(elements)))
}

/// Parse an S-expression with configurable precompilation behavior
fn parse_sexpr(
    input: &str,
    should_precompile: ShouldPrecompileOps,
    depth: usize,
) -> IResult<&str, Value> {
    if depth >= MAX_PARSE_DEPTH {
        return Err(nom::Err::Error(nom::error::Error::new(
            input,
            nom::error::ErrorKind::TooLarge,
        )));
    }
    preceded(
        multispace0,
        alt((
            |input| parse_quote(input, should_precompile, depth), // Pass precompilation setting to quote
            |input| parse_list(input, should_precompile, depth),
            parse_number,
            parse_bool,
            parse_string,
            parse_symbol,
        )),
    )
    .parse(input)
}

/// Parse quoted expression ('expr -> (quote expr))
fn parse_quote(
    input: &str,
    should_precompile: ShouldPrecompileOps,
    depth: usize,
) -> IResult<&str, Value> {
    let (input, _) = char('\'').parse(input)?;
    let (input, expr) = parse_sexpr(input, ShouldPrecompileOps::No, depth + 1)?; // Use unprecompiled parsing for quoted content

    // Create PrecompiledOp only if precompilation is enabled
    if should_precompile == ShouldPrecompileOps::Yes {
        let precompiled = create_quote_precompiled_op(&expr);
        return Ok((input, precompiled));
    }

    // Fallback to unprecompiled representation (only when precompilation disabled)
    Ok((
        input,
        Value::List(vec![Value::Symbol("quote".into()), expr]),
    ))
}

/// Parse a complete S-expression from input.
pub fn parse_scheme(input: &str) -> Result<Value, Error> {
    match terminated(
        |input| parse_sexpr(input, ShouldPrecompileOps::Yes, 0),
        multispace0,
    )
    .parse(input)
    {
        Ok(("", value)) => {
            // After successful parsing, validate arity for any PrecompiledOp
            validate_arity_in_ast(&value)?;
            Ok(value)
        }
        Ok((remaining, _)) => Err(Error::ParseError(format!(
            "Unexpected remaining input: '{remaining}'"
        ))),
        Err(e) => Err(Error::ParseError(parse_error_to_message(input, e))),
    }
}

/// Recursively validate arity in parsed AST - simpler than threading through parser
fn validate_arity_in_ast(value: &Value) -> Result<(), Error> {
    match value {
        Value::PrecompiledOp { op, args, .. } => {
            // Validate this operation's arity
            if let Err(Error::ArityError { expected, got, .. }) = op.validate_arity(args.len()) {
                return Err(Error::arity_error_with_expr(
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
#[expect(clippy::unwrap_used)] // test code OK
mod tests {
    use super::*;
    use crate::ast::{nil, sym, val};

    /// Test result variants for comprehensive parsing tests
    #[derive(Debug)]
    enum ParseTestResult {
        Success(Value), // Parsing should succeed with this value
        SuccessPrecompiledOp(&'static str, Vec<Value>), // Should succeed with PrecompiledOp(scheme_id, args)
        SemanticallyEquivalent(Value), // Should succeed and be semantically equivalent (for quote shorthand)
        SpecificError(&'static str),   // Parsing should fail with error containing this string
        Error,                         // Parsing should fail (any error)
    }
    use ParseTestResult::*;

    /// Helper for successful parse test cases
    fn success<T: Into<Value>>(value: T) -> ParseTestResult {
        Success(value.into())
    }

    /// Helper for PrecompiledOp test cases
    fn precompiled_op(scheme_id: &'static str, args: Vec<Value>) -> ParseTestResult {
        SuccessPrecompiledOp(scheme_id, args)
    }

    /// Helper for SemanticallyEquivalent test cases (used for quote shorthand)
    fn semantically_equivalent<T: Into<Value>>(value: T) -> ParseTestResult {
        SemanticallyEquivalent(value.into())
    }

    /// Run comprehensive parse tests with simplified error reporting and round-trip validation
    fn run_parse_tests(test_cases: Vec<(&str, ParseTestResult)>) {
        for (i, (input, expected)) in test_cases.iter().enumerate() {
            let test_id = format!("Parse test #{}", i + 1);
            let result = parse_scheme(input);

            match (result, expected) {
                // Success cases with round-trip testing
                (Ok(actual), Success(expected_val)) => {
                    assert_eq!(actual, *expected_val, "{test_id}: value mismatch");

                    // Test round-trip: display -> parse -> display should be identical
                    let displayed = format!("{actual}");
                    let reparsed = parse_scheme(&displayed).unwrap_or_else(|e| {
                        panic!("{test_id}: round-trip parse failed for '{displayed}': {e:?}")
                    });
                    let redisplayed = format!("{reparsed}");
                    assert_eq!(
                        displayed, redisplayed,
                        "{test_id}: round-trip display mismatch for '{input}'"
                    );
                }

                (Ok(actual), SuccessPrecompiledOp(expected_scheme_id, expected_args)) => {
                    if let Value::PrecompiledOp { op_id, args, .. } = &actual {
                        assert_eq!(op_id, expected_scheme_id, "{test_id}: scheme_id mismatch");
                        assert_eq!(args, expected_args, "{test_id}: args mismatch");

                        // Test round-trip for PrecompiledOp
                        let displayed = format!("{actual}");
                        let reparsed = parse_scheme(&displayed).unwrap_or_else(|e| {
                            panic!("{test_id}: round-trip parse failed for '{displayed}': {e:?}")
                        });
                        let redisplayed = format!("{reparsed}");
                        assert_eq!(
                            displayed, redisplayed,
                            "{test_id}: round-trip display mismatch for '{input}'"
                        );
                    } else {
                        panic!("{test_id}: expected PrecompiledOp, got {actual:?}");
                    }
                }

                (Ok(actual), SemanticallyEquivalent(expected_val)) => {
                    // For semantically equivalent cases, we compare the uncompiled forms
                    // This is useful for quote shorthand ('foo vs (quote foo))
                    let actual_uncompiled = actual.to_uncompiled_form();
                    assert_eq!(
                        actual_uncompiled, *expected_val,
                        "{test_id}: semantic equivalence mismatch"
                    );

                    // Test round-trip for SemanticallyEquivalent
                    let displayed = format!("{actual}");
                    let reparsed = parse_scheme(&displayed).unwrap_or_else(|e| {
                        panic!("{test_id}: round-trip parse failed for '{displayed}': {e:?}")
                    });
                    let redisplayed = format!("{reparsed}");
                    assert_eq!(
                        displayed, redisplayed,
                        "{test_id}: round-trip display mismatch for '{input}'"
                    );
                }

                // Error cases (success)
                (Err(_), Error) => {} // Generic error case passes
                (Err(err), SpecificError(expected_text)) => {
                    let error_msg = format!("{err:?}");
                    assert!(
                        error_msg.contains(expected_text),
                        "{test_id}: error should contain '{expected_text}'"
                    );
                }

                // Mismatched cases (failures)
                (Ok(actual), Error) => {
                    panic!("{test_id}: expected error, got {actual:?}");
                }
                (Ok(actual), SpecificError(expected_text)) => {
                    panic!(
                        "{test_id}: expected error containing '{expected_text}', got {actual:?}"
                    );
                }
                (Err(err), Success(_)) => {
                    panic!("{test_id}: expected success, got error {err:?}");
                }
                (Err(err), SuccessPrecompiledOp(_, _)) => {
                    panic!("{test_id}: expected PrecompiledOp, got error {err:?}");
                }
                (Err(err), SemanticallyEquivalent(_)) => {
                    panic!("{test_id}: expected SemanticallyEquivalent, got error {err:?}");
                }
            }
        }
    }

    #[test]
    #[expect(clippy::too_many_lines)] // Comprehensive test coverage is intentionally thorough
    fn test_parser_comprehensive() {
        use crate::builtinops::find_scheme_op;

        let test_cases = vec![
            // ===== NUMBER PARSING =====
            // Decimal numbers
            ("42", success(42)),
            ("-5", success(-5)),
            ("0", success(0)),
            ("-0", success(0)),
            // Hexadecimal numbers
            ("#x1A", success(26)),
            ("#X1a", success(26)), // Test case-insensitivity
            ("#xff", success(255)),
            ("#x0", success(0)),
            ("#x12345", success(74565)),
            // Edge cases - large integer literals
            ("9223372036854775807", success(i64::MAX)),
            ("-9223372036854775808", success(i64::MIN)),
            // Number parsing failures
            ("3.14", Error),                  // Floating point should fail
            ("#xG", Error),                   // Invalid hexadecimal should fail
            ("#x", Error),                    // Incomplete hex should fail
            ("#y123", Error),                 // Invalid hex prefix should fail
            ("123abc", Error),                // Mixed should fail
            ("99999999999999999999", Error),  // Too large for NumberType
            ("-99999999999999999999", Error), // Too small for NumberType
            // ===== SYMBOL PARSING =====
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
            ("test$name", success(sym("test$name"))),
            // Alphanumeric combinations
            ("var123", success(sym("var123"))),
            ("-", success(sym("-"))),
            ("-abc", success(sym("-abc"))),
            // Invalid symbol tests - numbers at start cause parse error, or invalid chars
            ("123var", Error),
            ("-42name", Error),
            ("test space", Error),
            ("test@home", Error),
            ("test#tag", Error),
            ("test%percent", Error),
            // ===== BOOLEAN PARSING =====
            // Valid booleans
            ("#t", success(true)),
            ("#f", success(false)),
            // Should fail - case sensitive
            ("#T", Error),
            ("#F", Error),
            ("#true", Error),
            ("#false", Error),
            // ===== STRING PARSING =====
            // Basic strings
            ("\"hello\"", success("hello")),
            ("\"hello world\"", success("hello world")),
            // Test escape sequences (using raw strings for clarity)
            (r#""hello\nworld""#, success("hello\nworld")),
            (r#""tab\there""#, success("tab\there")),
            (r#""carriage\rreturn""#, success("carriage\rreturn")),
            (r#""quote\"test""#, success("quote\"test")),
            (r#""backslash\\test""#, success("backslash\\test")),
            // Test unknown escape sequences (should fail)
            (r#""other\xchar""#, Error), // Unknown escape \x
            (r#""test\zchar""#, Error),  // Unknown escape \z
            // Test empty string
            ("\"\"", success("")),
            // Test unterminated string (should fail)
            (r#""unterminated"#, Error),
            (r#""unterminated\"#, Error), // ends with backslash
            (r#""test\""#, Error),        // string with just escape at end
            // ===== NIL PARSING =====
            ("()", success(nil())),
            // ===== LIST PARSING =====
            // Single element list
            ("(42)", success([42])),
            // Regular list with mixed types
            (
                "(1 hello \"world\" #t)",
                success([val(1), sym("hello"), val("world"), val(true)]),
            ),
            // Regular list (not a builtin operation)
            ("(1 2 3)", success([1, 2, 3])),
            // Test that builtin operations are parsed as PrecompiledOp
            ("(+ 1 2)", precompiled_op("+", vec![val(1), val(2)])),
            (
                "(* 3 4 5)",
                precompiled_op("*", vec![val(3), val(4), val(5)]),
            ),
            ("(< 1 2)", precompiled_op("<", vec![val(1), val(2)])),
            (
                "(if #t 1 2)",
                precompiled_op("if", vec![val(true), val(1), val(2)]),
            ),
            // Test that non-builtin symbols still create regular lists
            ("(foo 1 2)", success([sym("foo"), val(1), val(2)])),
            // Test list with only symbols (should remain a list)
            ("(a b c)", success([sym("a"), sym("b"), sym("c")])),
            // Test list starting with number (should remain a list)
            (
                "(42 is the answer)",
                success([val(42), sym("is"), sym("the"), sym("answer")]),
            ),
            // ===== QUOTE PARSING =====
            // Quote shorthand - semantically equivalent to longhand
            (
                "'foo",
                semantically_equivalent(val([sym("quote"), sym("foo")])),
            ),
            (
                "'(1 2 3)",
                semantically_equivalent(val([sym("quote"), val([1, 2, 3])])),
            ),
            ("'()", semantically_equivalent(val([sym("quote"), nil()]))),
            // Longhand quote syntax - should create PrecompiledOp
            ("(quote foo)", precompiled_op("quote", vec![sym("foo")])),
            (
                "(quote (1 2 3))",
                precompiled_op("quote", vec![val([1, 2, 3])]),
            ),
            // ===== NESTED LIST PARSING =====
            ("((1 2) (3 4))", success([[1, 2], [3, 4]])),
            // Test nested lists with mixed builtins and regular lists
            (
                "((+ 1 2) (foo bar))",
                success([
                    val(Value::PrecompiledOp {
                        op: find_scheme_op("+").unwrap(),
                        op_id: "+".into(),
                        args: vec![val(1), val(2)],
                    }),
                    val([sym("foo"), sym("bar")]),
                ]),
            ),
            // Test nested expressions that should parse successfully
            (
                "(car (list 1 2 3))",
                precompiled_op(
                    "car",
                    vec![val(Value::PrecompiledOp {
                        op: find_scheme_op("list").unwrap(),
                        op_id: "list".into(),
                        args: vec![val(1), val(2), val(3)],
                    })],
                ),
            ),
            // ===== WHITESPACE HANDLING =====
            // Test various whitespace scenarios
            ("  42  ", success(42)),
            ("\t#t\n", success(true)),
            ("\r\n  foo  \t", success(sym("foo"))),
            // Lists with various whitespace
            ("( 1   2\t\n3 )", success([1, 2, 3])),
            // Empty list with whitespace
            ("(   )", success(nil())),
            ("(\t\n)", success(nil())),
            // ===== COMPLEX NESTED STRUCTURES =====
            // Deeply nested lists
            ("(((1)))", success([val([val([val(1)])])])),
            // Mixed types in nested structure
            (
                "(foo (\"bar\" #t) -123)",
                success([sym("foo"), val([val("bar"), val(true)]), val(-123)]),
            ),
            // ===== GENERAL ERROR CASES =====
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
            // ===== PARSE-TIME ARITY ERRORS =====
            // Special forms with strict arity requirements

            // SCHEME-JSONLOGIC-STRICT: Require exactly 3 arguments
            // (Scheme allows 2 args with undefined behavior, JSONLogic allows chaining with >3 args)
            // 'if' requires exactly 3 arguments
            ("(if #t 1)", SpecificError("ArityError")), // Too few args
            ("(if #t 42 0 extra)", SpecificError("ArityError")), // Too many args
            ("(if)", SpecificError("ArityError")),      // No args
            // 'and' requires at least 1 argument
            ("(and)", SpecificError("ArityError")), // No args
            // 'or' requires at least 1 argument
            ("(or)", SpecificError("ArityError")), // No args
            // 'not' requires exactly 1 argument
            ("(not)", SpecificError("ArityError")), // No args
            ("(not #t #f)", SpecificError("ArityError")), // Too many args
            // 'car' requires exactly 1 argument
            ("(car)", SpecificError("ArityError")), // No args
            ("(car (list 1 2) extra)", SpecificError("ArityError")), // Too many args
            // 'cdr' requires exactly 1 argument
            ("(cdr)", SpecificError("ArityError")), // No args
            ("(cdr (list 1 2) extra)", SpecificError("ArityError")), // Too many args
            // Valid cases with correct arity should parse as PrecompiledOps
            (
                "(if #t 1 2)",
                precompiled_op("if", vec![val(true), val(1), val(2)]),
            ),
            (
                "(and #t #f)",
                precompiled_op("and", vec![val(true), val(false)]),
            ),
            (
                "(or #f #t)",
                precompiled_op("or", vec![val(false), val(true)]),
            ),
            ("(not #f)", precompiled_op("not", vec![val(false)])),
            // Test nested arity errors are also caught
            ("(list (not) 42)", SpecificError("ArityError")),
            // ===== PARSE-TIME SYNTAX ERRORS =====
            // Unclosed parentheses - should contain parse error information
            ("(+ 1 (- 2", SpecificError("ParseError")),
            // Extra closing parentheses
            ("1 2 3)", SpecificError("ParseError")),
            ("(1 2))", SpecificError("ParseError")),
            // Invalid starting characters
            (")", SpecificError("ParseError")),
            // ===== DEPTH LIMIT TESTS =====
            // Test that deeply nested expressions are rejected (MAX_PARSE_DEPTH = 32)
            // This prevents stack overflow attacks from deeply nested structures
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
            ("symbol", success(sym("symbol"))), // Raw symbol, not quoted
        ];

        run_parse_tests(test_cases);
    }

    #[test]
    fn test_parser_depth_limits() {
        // Create depth limit test strings
        let parens_under_limit = format!(
            "{}unbound{}",
            "(".repeat(MAX_PARSE_DEPTH - 1),
            ")".repeat(MAX_PARSE_DEPTH - 1)
        );
        let quotes_under_limit = format!("{}unbound", "'".repeat(MAX_PARSE_DEPTH - 1));
        let deep_parens_at_limit = format!(
            "{}1{}",
            "(".repeat(MAX_PARSE_DEPTH),
            ")".repeat(MAX_PARSE_DEPTH)
        );
        let deep_quotes_at_limit = format!("{}a", "'".repeat(MAX_PARSE_DEPTH));

        let depth_test_cases = vec![
            // At/over limit should fail at parse time with specific error
            (
                deep_parens_at_limit.as_str(),
                SpecificError("Invalid syntax"),
            ),
            (
                deep_quotes_at_limit.as_str(),
                SpecificError("Invalid syntax"),
            ),
        ];

        run_parse_tests(depth_test_cases);

        // Verify that expressions just under the limit parse successfully
        assert!(
            parse_scheme(&parens_under_limit).is_ok(),
            "Parens just under depth limit should parse successfully"
        );
        assert!(
            parse_scheme(&quotes_under_limit).is_ok(),
            "Quotes just under depth limit should parse successfully"
        );
    }
}
