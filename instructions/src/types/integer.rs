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
use snarkvm_circuits::{
    traits::{Eject, IntegerTrait},
    Environment,
    Integer as IntegerCircuit,
    IntegerType,
    Mode,
};

use core::iter::FromIterator;
use nom::{
    bytes::complete::tag,
    character::complete::{char, one_of},
    combinator::{map_res, verify},
    multi::{many0, many1},
    sequence::terminated,
};

pub struct Integer<E: Environment, I: IntegerType>(IntegerCircuit<E, I>);

impl<E: Environment, I: IntegerType> Integer<E, I> {
    pub fn new(input: &str) -> ParserResult<Self> {
        // Parse the digits from the input.
        let (input, value) =
            map_res(many1(terminated(one_of("0123456789"), many0(char('_')))), |v| String::from_iter(v).parse::<I>())(
                input,
            )?;
        // Parse the integer type from the input, and ensure it matches the declared `IntegerType`.
        let (input, _) = verify(tag(I::type_name()), |t: &str| t == I::type_name())(input)?;
        // Output the remaining input and the initialized integer.
        Ok((input, Self(IntegerCircuit::new(Mode::Constant, value))))
    }

    pub fn to_value(&self) -> I {
        self.0.eject_value()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits::Circuit;

    #[test]
    fn test_u8() {
        type E = Circuit;
        type I = u8;
        assert_eq!(5u8, Integer::<E, I>::new("5u8").unwrap().1.to_value());
        assert_eq!(5u8, Integer::<E, I>::new("5_u8").unwrap().1.to_value());
        assert_eq!(15u8, Integer::<E, I>::new("1_5_u8").unwrap().1.to_value());
    }

    #[test]
    fn test_malformed_integer() {
        assert!(Integer::<Circuit, u8>::new("5u_8").is_err());
    }
}
