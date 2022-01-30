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
use snarkvm_circuits::{Affine, Eject, Environment, Mode};

use core::iter::FromIterator;
use nom::{
    bytes::complete::tag,
    character::complete::{char, one_of},
    combinator::{map_res, verify},
    multi::{many0, many1},
    sequence::terminated,
};

pub struct Group<E: Environment>(Affine<E>);

impl<E: Environment> Group<E> {
    pub fn new(input: &str) -> ParserResult<Self> {
        // Parse the digits from the input.
        let (input, x_coordinate) = map_res(many1(terminated(one_of("0123456789"), many0(char('_')))), |v| {
            String::from_iter(v).parse::<E::BaseField>()
        })(input)?;
        // Parse the group type from the input, and ensure it matches the group type.
        let (input, _) = verify(tag("group"), |t: &str| t == "group")(input)?;
        // Output the remaining input and the initialized group constant.
        Ok((input, Self(Affine::new(Mode::Constant, x_coordinate, None))))
    }

    pub fn to_value(&self) -> E::Affine {
        self.0.eject_value()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits::Circuit;

    use core::str::FromStr;

    #[test]
    fn test_group_new() {
        type E = Circuit;
        assert_eq!(
            E::affine_from_x_coordinate(<E as Environment>::BaseField::from_str("0").unwrap()),
            Group::<E>::new("0group").unwrap().1.to_value()
        );
        assert_eq!(
            E::affine_from_x_coordinate(<E as Environment>::BaseField::from_str("0").unwrap()),
            Group::<E>::new("0_group").unwrap().1.to_value()
        );
    }

    #[test]
    fn test_malformed_group() {
        type E = Circuit;
        assert!(Group::<E>::new("0grou_p").is_err());
    }
}
