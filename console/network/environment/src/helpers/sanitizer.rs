// Copyright (C) 2019-2022 Aleo Systems Inc.
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

use crate::ParserResult;

use nom::{
    branch::alt,
    bytes::complete::{tag, take_until},
    character::complete::{anychar, char, line_ending, multispace1},
    combinator::{cut, map, recognize, value},
    error::{ErrorKind, VerboseError, VerboseErrorKind},
    multi::fold_many0,
    sequence::{preceded, terminated},
};

pub struct Sanitizer;

impl Sanitizer {
    /// Removes all leading whitespaces and comments from the given input, returning the sanitized input.
    pub fn parse(string: &str) -> ParserResult<&str> {
        preceded(Self::parse_whitespaces, Self::parse_comments)(string)
    }

    /// Removes leading whitespaces from the given input.
    pub fn parse_whitespaces(string: &str) -> ParserResult<&str> {
        recognize(Self::many0_(alt((multispace1, tag("\\\n")))))(string)
    }

    /// Removes multiple leading comments from the given input.
    pub fn parse_comments(string: &str) -> ParserResult<&str> {
        recognize(Self::many0_(terminated(Self::parse_comment, Self::parse_whitespaces)))(string)
    }

    /// Removes the first leading comment from the given input.
    pub fn parse_comment(string: &str) -> ParserResult<&str> {
        preceded(
            char('/'),
            alt((
                preceded(char('/'), cut(Self::str_till_eol)),
                preceded(char('*'), cut(terminated(take_until("*/"), tag("*/")))),
            )),
        )(string)
    }
}

impl Sanitizer {
    /// End-of-input parser.
    ///
    /// Yields `()` if the parser is at the end of the input; an error otherwise.
    fn eoi(string: &str) -> ParserResult<()> {
        match string.is_empty() {
            true => Ok((string, ())),
            false => {
                Err(nom::Err::Error(VerboseError { errors: vec![(string, VerboseErrorKind::Nom(ErrorKind::Eof))] }))
            }
        }
    }

    /// A newline parser that accepts:
    ///
    /// - A newline.
    /// - The end of input.
    fn eol(string: &str) -> ParserResult<()> {
        alt((
            Self::eoi, // this one goes first because it’s very cheap
            value((), line_ending),
        ))(string)
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
    fn str_till_eol(string: &str) -> ParserResult<&str> {
        map(recognize(Self::till(alt((value((), tag("\\\n")), value((), anychar))), Self::eol)), |i| {
            if i.as_bytes().last() == Some(&b'\n') { &i[0..i.len() - 1] } else { i }
        })(string)
    }

    /// A version of many0 that discards the result of the parser, preventing allocating.
    fn many0_<'a, A, F>(mut f: F) -> impl FnMut(&'a str) -> ParserResult<'a, ()>
    where
        F: FnMut(&'a str) -> ParserResult<'a, A>,
    {
        move |string| fold_many0(&mut f, || (), |_, _| ())(string)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sanitize() {
        // Whitespaces
        assert_eq!(("hello world", ""), Sanitizer::parse("hello world").unwrap());
        assert_eq!(("hello world", ""), Sanitizer::parse(" hello world").unwrap());
        assert_eq!(("hello world", ""), Sanitizer::parse("  hello world").unwrap());
        assert_eq!(("hello world", ""), Sanitizer::parse("\nhello world").unwrap());
        assert_eq!(("hello world", ""), Sanitizer::parse(" \nhello world").unwrap());
        assert_eq!(("hello world ", ""), Sanitizer::parse("hello world ").unwrap());

        // Comments
        assert_eq!(("hello world", "// hello\n"), Sanitizer::parse("// hello\nhello world").unwrap());
        assert_eq!(("hello world", "/* hello */"), Sanitizer::parse("/* hello */hello world").unwrap());
        assert_eq!(("hello world", "/* hello */\n"), Sanitizer::parse("/* hello */\nhello world").unwrap());
        assert_eq!(("hello world", "/** hello */"), Sanitizer::parse("/** hello */hello world").unwrap());
        assert_eq!(("hello world", "/** hello */\n"), Sanitizer::parse("/** hello */\nhello world").unwrap());
        assert_eq!(("/\nhello world", ""), Sanitizer::parse("/\nhello world").unwrap());

        // Whitespaces and comments
        assert_eq!(("hello world", "// hello\n"), Sanitizer::parse(" \n// hello\nhello world").unwrap());
        assert_eq!(("hello world", "/* hello */\n"), Sanitizer::parse(" \n /* hello */\nhello world").unwrap());
        assert_eq!(("hello world", "/** hello */\n"), Sanitizer::parse(" \n\t  /** hello */\nhello world").unwrap());
        assert_eq!(("/\nhello world", ""), Sanitizer::parse(" /\nhello world").unwrap());
    }

    #[test]
    fn test_whitespaces() {
        assert_eq!(("hello world", ""), Sanitizer::parse_whitespaces("hello world").unwrap());
        assert_eq!(("hello world", " "), Sanitizer::parse_whitespaces(" hello world").unwrap());
        assert_eq!(("hello world", "  "), Sanitizer::parse_whitespaces("  hello world").unwrap());
        assert_eq!(("hello world", "\n"), Sanitizer::parse_whitespaces("\nhello world").unwrap());
        assert_eq!(("hello world", " \n"), Sanitizer::parse_whitespaces(" \nhello world").unwrap());
        assert_eq!(("hello world", "\t"), Sanitizer::parse_whitespaces("\thello world").unwrap());
        assert_eq!(("hello world", " \t"), Sanitizer::parse_whitespaces(" \thello world").unwrap());
        assert_eq!(("hello world", " \n\t"), Sanitizer::parse_whitespaces(" \n\thello world").unwrap());
        assert_eq!(("hello world ", ""), Sanitizer::parse_whitespaces("hello world ").unwrap());
    }

    #[test]
    fn test_comments() {
        assert_eq!(("hello world", "// hello\n"), Sanitizer::parse_comments("// hello\nhello world").unwrap());
        assert_eq!(("hello world", "/* hello */\n"), Sanitizer::parse_comments("/* hello */\nhello world").unwrap());
        assert_eq!(("hello world", "/** hello */\n"), Sanitizer::parse_comments("/** hello */\nhello world").unwrap());
        assert_eq!(("/\nhello world", ""), Sanitizer::parse_comments("/\nhello world").unwrap());
    }
}
