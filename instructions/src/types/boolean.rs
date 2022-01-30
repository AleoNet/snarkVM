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

use crate::{keyword, ParserResult};

use nom::{branch::alt, combinator::value};

pub struct Boolean(bool);

impl Boolean {
    pub fn new(input: &str) -> ParserResult<Self> {
        // Parse the boolean from the input.
        let (input, boolean) = alt((value(true, keyword("true")), value(false, keyword("false"))))(input)?;
        // Output the remaining input and the initialized boolean.
        Ok((input, Self(boolean)))
    }

    pub fn to_value(&self) -> bool {
        self.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_boolean_new() {
        assert_eq!(true, Boolean::new("true").unwrap().1.to_value());
        assert_eq!(false, Boolean::new("false").unwrap().1.to_value());
    }

    #[test]
    fn test_malformed_boolean() {
        assert!(Boolean::new("maybe").is_err());
        assert!(Boolean::new("truee").is_err());
        assert!(Boolean::new("truefalse").is_err());
        assert!(Boolean::new("falsetrue").is_err());
    }
}
