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

use crate::ParserResult;
use snarkvm_curves::edwards_bls12::Fq;
use snarkvm_fields::FieldError;

use nom::{
    bytes::complete::tag,
    character::complete::{char, one_of},
    combinator::verify,
    multi::{many0, many1},
    sequence::terminated,
};

pub struct Base(Fq);

impl Base {
    pub fn new(input: &str) -> ParserResult<Result<Self, FieldError>> {
        // Parse the digits from the input.
        let (input, value) = many1(terminated(one_of("0123456789"), many0(char('_'))))(input)?;
        // Parse the base field type from the input, and ensure it matches the field type.
        let (input, _) = verify(tag("base"), |t: &str| t == "base")(input)?;
        // Initialize the base field.
        let base = value
            .into_iter()
            .collect::<String>()
            .parse::<Fq>()
            .and_then(|v| Ok(Self(v)));
        // Output the remaining input and the initialized base field.
        Ok((input, base))
    }

    pub fn to_value(&self) -> Fq {
        self.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::str::FromStr;

    #[test]
    fn test_base_new() {
        assert_eq!(
            Fq::from_str("5").unwrap(),
            Base::new("5base").unwrap().1.unwrap().to_value()
        );
        assert_eq!(
            Fq::from_str("5").unwrap(),
            Base::new("5_base").unwrap().1.unwrap().to_value()
        );
        assert_eq!(
            Fq::from_str("15").unwrap(),
            Base::new("1_5_base").unwrap().1.unwrap().to_value()
        );
    }

    #[test]
    fn test_malformed_base() {
        assert!(Base::new("5ba_se").is_err());
    }
}
