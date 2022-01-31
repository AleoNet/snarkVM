// Copyright (C) 2019-2021 Aleo Systems Inc.
// This file is part of the snarkVM library.

// The snarkVM library is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// The snarkVM library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with the snarkVM library. If not, see <https://www.gnu.org/licenses/>.

use nom::{
    branch::alt,
    bytes::complete::{tag, take_until},
    character::complete::{anychar, char, line_ending, multispace1},
    combinator::{cut, map, not, peek, recognize, value, verify},
    error::{ErrorKind, VerboseError, VerboseErrorKind},
    multi::fold_many0,
    sequence::{preceded, terminated},
    IResult,
};

pub type ParserResult<'a, O> = IResult<&'a str, O, VerboseError<&'a str>>;

/// Removes all leading whitespaces and comments from the given input, returning the sanitized input.
pub fn sanitize(i: &str) -> ParserResult<&str> {
    preceded(whitespaces, comments)(i)
}

/// Removes leading whitespaces from the given input.
pub fn whitespaces(input: &str) -> ParserResult<&str> {
    recognize(many0_(alt((multispace1, tag("\\\n")))))(input)
}

/// Removes the first leading comment from the given input.
pub fn comment(input: &str) -> ParserResult<&str> {
    preceded(
        char('/'),
        alt((
            preceded(char('/'), cut(str_till_eol)),
            preceded(char('*'), cut(terminated(take_until("*/"), tag("*/")))),
        )),
    )(input)
}

/// Removes multiple leading comments from the given input.
pub fn comments(input: &str) -> ParserResult<&str> {
    recognize(many0_(terminated(comment, whitespaces)))(input)
}

/// Enforces the input is a keyword, meaning the character after the keyword does not imply a continuation (is_alphanumeric or '_').
pub fn keyword<'a>(input: &'a str) -> impl FnMut(&'a str) -> ParserResult<&'a str> {
    terminated(tag(input), not(verify(peek(anychar), |&c| c.is_alphanumeric() || c == '_')))
}

/// End-of-input parser.
///
/// Yields `()` if the parser is at the end of the input; an error otherwise.
fn eoi(input: &str) -> ParserResult<()> {
    match input.is_empty() {
        true => Ok((input, ())),
        false => Err(nom::Err::Error(VerboseError { errors: vec![(input, VerboseErrorKind::Nom(ErrorKind::Eof))] })),
    }
}

/// A newline parser that accepts:
///
/// - A newline.
/// - The end of input.
fn eol(input: &str) -> ParserResult<()> {
    alt((
        eoi, // this one goes first because it’s very cheap
        value((), line_ending),
    ))(input)
}

/// Apply the `f` parser until `g` succeeds. Both parsers consume the input.
fn till<'a, A, B, F, G>(mut f: F, mut g: G) -> impl FnMut(&'a str) -> ParserResult<'a, ()>
where
    F: FnMut(&'a str) -> ParserResult<'a, A>,
    G: FnMut(&'a str) -> ParserResult<'a, B>,
{
    move |mut i| loop {
        if let Ok((i2, _)) = g(i) {
            break Ok((i2, ()));
        }

        let (i2, _) = f(i)?;
        i = i2;
    }
}

/// Parse a string until the end of line.
///
/// This parser accepts the multiline annotation (\) to break the string on several lines.
///
/// Discard any leading newline.
fn str_till_eol(input: &str) -> ParserResult<&str> {
    map(recognize(till(alt((value((), tag("\\\n")), value((), anychar))), eol)), |i| {
        if i.as_bytes().last() == Some(&b'\n') { &i[0..i.len() - 1] } else { i }
    })(input)
}

/// A version of many0 that discards the result of the parser, preventing allocating.
fn many0_<'a, A, F>(mut f: F) -> impl FnMut(&'a str) -> ParserResult<'a, ()>
where
    F: FnMut(&'a str) -> ParserResult<'a, A>,
{
    move |i| fold_many0(&mut f, || (), |_, _| ())(i)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sanitize() {
        assert_eq!(("hello world", ""), sanitize("hello world").unwrap());
        assert_eq!(("hello world", ""), sanitize(" hello world").unwrap());
        assert_eq!(("hello world", ""), sanitize("  hello world").unwrap());
        assert_eq!(("hello world", ""), sanitize("\nhello world").unwrap());
        assert_eq!(("hello world", ""), sanitize(" \nhello world").unwrap());
        assert_eq!(("hello world ", ""), sanitize("hello world ").unwrap());

        assert_eq!(("hello world", "// hello\n"), sanitize("// hello\nhello world").unwrap());
        assert_eq!(("hello world", "/* hello */\n"), sanitize("/* hello */\nhello world").unwrap());
        assert_eq!(("hello world", "/** hello */\n"), sanitize("/** hello */\nhello world").unwrap());
        assert_eq!(("/\nhello world", ""), sanitize("/\nhello world").unwrap());
    }

    #[test]
    fn test_whitespaces() {
        assert_eq!(("hello world", ""), whitespaces("hello world").unwrap());
        assert_eq!(("hello world", " "), whitespaces(" hello world").unwrap());
        assert_eq!(("hello world", "  "), whitespaces("  hello world").unwrap());
        assert_eq!(("hello world", "\n"), whitespaces("\nhello world").unwrap());
        assert_eq!(("hello world", " \n"), whitespaces(" \nhello world").unwrap());
        assert_eq!(("hello world ", ""), whitespaces("hello world ").unwrap());
    }

    #[test]
    fn test_comments() {
        assert_eq!(("hello world", "// hello\n"), comments("// hello\nhello world").unwrap());
        assert_eq!(("hello world", "/* hello */\n"), comments("/* hello */\nhello world").unwrap());
        assert_eq!(("hello world", "/** hello */\n"), comments("/** hello */\nhello world").unwrap());
        assert_eq!(("/\nhello world", ""), comments("/\nhello world").unwrap());
    }
}
