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
use snarkvm_curves::edwards_bls12::Fr;
use snarkvm_fields::FieldError;

use nom::{
    bytes::complete::tag,
    character::complete::{char, one_of},
    combinator::verify,
    multi::{many0, many1},
    sequence::terminated,
};

pub struct Scalar(Fr);

impl Scalar {
    pub fn new(input: &str) -> ParserResult<Result<Self, FieldError>> {
        // Parse the digits from the input.
        let (input, value) = many1(terminated(one_of("0123456789"), many0(char('_'))))(input)?;
        // Parse the scalar field type from the input, and ensure it matches the field type.
        let (input, _) = verify(tag("scalar"), |t: &str| t == "scalar")(input)?;
        // Output the remaining input and the initialized scalar field.
        Ok((
            input,
            value
                .into_iter()
                .collect::<String>()
                .parse::<Fr>()
                .and_then(|v| Ok(Self(v))),
        ))
    }

    pub fn to_value(&self) -> Fr {
        self.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::str::FromStr;

    #[test]
    fn test_scalar_new() {
        assert_eq!(
            Fr::from_str("5").unwrap(),
            Scalar::new("5scalar").unwrap().1.unwrap().to_value()
        );
        assert_eq!(
            Fr::from_str("5").unwrap(),
            Scalar::new("5_scalar").unwrap().1.unwrap().to_value()
        );
        assert_eq!(
            Fr::from_str("15").unwrap(),
            Scalar::new("1_5_scalar").unwrap().1.unwrap().to_value()
        );
    }

    #[test]
    fn test_malformed_scalar() {
        assert!(Scalar::new("5scala_r").is_err());
    }
}
