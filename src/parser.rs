use nom::{
    branch::alt,
    bytes::complete::{tag, take_while1},
    character::complete::{char, multispace0, multispace1},
    combinator::{map, opt, recognize, value},
    error::{Error, ErrorKind},
    multi::separated_list0,
    sequence::{delimited, pair, preceded, terminated},
    IResult,
};

use crate::{SchemeError, Value};

/// Convert nom parsing errors to user-friendly messages
fn parse_error_to_message(input: &str, error: nom::Err<Error<&str>>) -> String {
    match error {
        nom::Err::Error(e) | nom::Err::Failure(e) => {
            let position = input.len().saturating_sub(e.input.len());
            match e.code {
                ErrorKind::TakeWhile1 => {
                    if input.trim_start().starts_with('(') && !input.contains(')') {
                        "Missing closing parenthesis".to_string()
                    } else if input.trim_start().starts_with(')') {
                        "Unexpected closing parenthesis".to_string()
                    } else {
                        format!("Invalid character at position {}", position)
                    }
                }
                ErrorKind::Char => format!("Expected character at position {}", position),
                ErrorKind::Tag => format!("Unexpected token at position {}", position),
                _ => {
                    if position < input.len() {
                        format!("Invalid syntax near '{}'", &input[position..].chars().take(10).collect::<String>())
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
        take_while1(|c: char| c.is_ascii_digit())
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
            break;
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
    
    Ok((remaining, Value::String(chars.into_iter().collect())))
}

/// Parse quoted expression ('expr -> (quote expr))
fn parse_quote(input: &str) -> IResult<&str, Value> {
    let (input, _) = char('\'')(input)?;
    let (input, expr) = parse_sexpr(input)?;
    Ok((input, Value::List(vec![
        Value::Symbol("quote".to_string()),
        expr,
    ])))
}

/// Parse an S-expression
fn parse_sexpr(input: &str) -> IResult<&str, Value> {
    preceded(
        multispace0,
        alt((
            parse_quote,
            parse_list,
            parse_number,
            parse_bool,
            parse_string,
            parse_symbol,
        )),
    )(input)
}

/// Parse a list
fn parse_list(input: &str) -> IResult<&str, Value> {
    delimited(
        char('('),
        map(
            preceded(
                multispace0,
                separated_list0(multispace1, parse_sexpr)
            ),
            Value::List,
        ),
        preceded(multispace0, char(')')),
    )(input)
}

/// Parse a complete S-expression from input
pub fn parse(input: &str) -> Result<Value, SchemeError> {
    match terminated(parse_sexpr, multispace0)(input) {
        Ok(("", value)) => Ok(value),
        Ok((remaining, _)) => Err(SchemeError::ParseError(format!(
            "Unexpected remaining input: '{}'",
            remaining
        ))),
        Err(e) => Err(SchemeError::ParseError(parse_error_to_message(input, e))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_number() {
        // Decimal numbers
        assert_eq!(parse("42").unwrap(), Value::Number(42));
        assert_eq!(parse("-5").unwrap(), Value::Number(-5));
        
        // Hexadecimal numbers
        assert_eq!(parse("#x1A").unwrap(), Value::Number(26));
        assert_eq!(parse("#X1a").unwrap(), Value::Number(26));
        assert_eq!(parse("#xff").unwrap(), Value::Number(255));
        assert_eq!(parse("#xFF").unwrap(), Value::Number(255));
        assert_eq!(parse("#x0").unwrap(), Value::Number(0));
        assert_eq!(parse("#x12345").unwrap(), Value::Number(74565));
        
        // Floating point should fail to parse
        assert!(parse("3.14").is_err());
        
        // Invalid hexadecimal should fail
        assert!(parse("#xG").is_err());
        assert!(parse("#x").is_err());
    }

    #[test]
    fn test_parse_bool() {
        assert_eq!(parse("#t").unwrap(), Value::Bool(true));
        assert_eq!(parse("#f").unwrap(), Value::Bool(false));
    }

    #[test]
    fn test_parse_symbol() {
        assert_eq!(parse("foo").unwrap(), Value::Symbol("foo".to_string()));
        assert_eq!(parse("+").unwrap(), Value::Symbol("+".to_string()));
        assert_eq!(parse(">=").unwrap(), Value::Symbol(">=".to_string()));
    }

    #[test]
    fn test_parse_string() {
        assert_eq!(parse("\"hello\"").unwrap(), Value::String("hello".to_string()));
        assert_eq!(parse("\"hello world\"").unwrap(), Value::String("hello world".to_string()));
    }

    #[test]
    fn test_parse_nil() {
        assert_eq!(parse("()").unwrap(), Value::List(vec![]));
    }

    #[test]
    fn test_parse_quote() {
        // Test quote shorthand
        assert_eq!(
            parse("'foo").unwrap(),
            Value::List(vec![
                Value::Symbol("quote".to_string()),
                Value::Symbol("foo".to_string())
            ])
        );
        
        // Test quote with list
        assert_eq!(
            parse("'(1 2 3)").unwrap(),
            Value::List(vec![
                Value::Symbol("quote".to_string()),
                Value::List(vec![
                    Value::Number(1),
                    Value::Number(2),
                    Value::Number(3)
                ])
            ])
        );
        
        // Test quote with nil
        assert_eq!(
            parse("'()").unwrap(),
            Value::List(vec![
                Value::Symbol("quote".to_string()),
                Value::List(vec![])
            ])
        );
    }

    #[test]
    fn test_parse_list() {
        assert_eq!(
            parse("(1 2 3)").unwrap(),
            Value::List(vec![
                Value::Number(1),
                Value::Number(2),
                Value::Number(3)
            ])
        );
        
        assert_eq!(
            parse("(+ 1 2)").unwrap(),
            Value::List(vec![
                Value::Symbol("+".to_string()),
                Value::Number(1),
                Value::Number(2)
            ])
        );
    }

    #[test]
    fn test_parse_nested_list() {
        assert_eq!(
            parse("((1 2) (3 4))").unwrap(),
            Value::List(vec![
                Value::List(vec![Value::Number(1), Value::Number(2)]),
                Value::List(vec![Value::Number(3), Value::Number(4)])
            ])
        );
    }
}