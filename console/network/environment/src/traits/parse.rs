// Copyright (C) 2019-2023 Aleo Systems Inc.
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
    error::{convert_error, VerboseError},
    Err as NomErr,
    IResult,
};

/// The `nom`-compatible parser return type.
pub type ParserResult<'a, O> = IResult<&'a str, O, VerboseError<&'a str>>;

/// Converts a `ParserResult` into a human-readable message.
pub fn convert_result<'a, O>(result: ParserResult<'a, O>, input: &'a str) -> String {
    match result {
        Ok(_) => "Parsing was successful.".to_string(),
        Err(error) => match error {
            NomErr::Incomplete(_) => "Parsing failed to consume the entire input.".to_string(),
            NomErr::Error(err) | NomErr::Failure(err) => convert_error(input, err),
        },
    }
}

/// Operations to parse a string literal into an object.
pub trait Parser: core::fmt::Display + core::str::FromStr {
    /// Parses a string literal into an object.
    fn parse(string: &str) -> ParserResult<Self>
    where
        Self: Sized;
}
