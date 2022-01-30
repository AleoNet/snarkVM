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
use snarkvm_circuits::{fields::BaseField, Eject, Environment, Mode};
use snarkvm_fields::FieldError;

use nom::{
    bytes::complete::tag,
    character::complete::{char, one_of},
    combinator::verify,
    multi::{many0, many1},
    sequence::terminated,
};

pub struct Base<E: Environment>(BaseField<E>);

impl<E: Environment> Base<E> {
    pub fn new(input: &str) -> ParserResult<Result<Self, FieldError>> {
        // Parse the digits from the input.
        let (input, value) = many1(terminated(one_of("0123456789"), many0(char('_'))))(input)?;
        // Parse the base field type from the input, and ensure it matches the field type.
        let (input, _) = verify(tag("base"), |t: &str| t == "base")(input)?;
        // Initialize the base field constant.
        let base = value
            .into_iter()
            .collect::<String>()
            .parse::<E::BaseField>()
            .and_then(|v| Ok(Self(BaseField::new(Mode::Constant, v))));
        // Output the remaining input and the initialized base field constant.
        Ok((input, base))
    }

    pub fn to_value(&self) -> E::BaseField {
        self.0.eject_value()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits::Circuit;

    use core::str::FromStr;

    #[test]
    fn test_base_new() {
        type E = Circuit;
        assert_eq!(
            <E as Environment>::BaseField::from_str("5").unwrap(),
            Base::<E>::new("5base").unwrap().1.unwrap().to_value()
        );
        assert_eq!(
            <E as Environment>::BaseField::from_str("5").unwrap(),
            Base::<E>::new("5_base").unwrap().1.unwrap().to_value()
        );
        assert_eq!(
            <E as Environment>::BaseField::from_str("15").unwrap(),
            Base::<E>::new("1_5_base").unwrap().1.unwrap().to_value()
        );
    }

    #[test]
    fn test_malformed_base() {
        type E = Circuit;
        assert!(Base::<E>::new("5ba_se").is_err());
    }
}
