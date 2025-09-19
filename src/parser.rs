use nom::{
    branch::alt,
    bytes::complete::{tag, take_while1},
    character::complete::{char, multispace0, multispace1},
    combinator::{map, opt, recognize, value},
    multi::separated_list0,
    sequence::{delimited, pair, preceded, terminated},
    IResult,
};

use crate::{SchemeError, Value};

/// Parse optional whitespace
fn opt_whitespace(input: &str) -> IResult<&str, ()> {
    value((), multispace0)(input)
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
    let symbol_char = |c: char| {
        c.is_alphanumeric() 
            || "+-*/<>=!?_".contains(c)
    };
    
    map(
        take_while1(symbol_char),
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

/// Parse nil (empty list)
fn parse_nil(input: &str) -> IResult<&str, Value> {
    value(Value::Nil, tag("()"))(input)
}

/// Parse an S-expression
fn parse_sexpr(input: &str) -> IResult<&str, Value> {
    preceded(
        opt_whitespace,
        alt((
            parse_nil,
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
            separated_list0(multispace1, parse_sexpr),
            Value::List,
        ),
        preceded(opt_whitespace, char(')')),
    )(input)
}

/// Parse a complete S-expression from input
pub fn parse(input: &str) -> Result<Value, SchemeError> {
    match terminated(parse_sexpr, opt_whitespace)(input) {
        Ok(("", value)) => Ok(value),
        Ok((remaining, _)) => Err(SchemeError::ParseError(format!(
            "Unexpected remaining input: {}",
            remaining
        ))),
        Err(e) => Err(SchemeError::ParseError(format!("Parse error: {}", e))),
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
        assert_eq!(parse("()").unwrap(), Value::Nil);
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