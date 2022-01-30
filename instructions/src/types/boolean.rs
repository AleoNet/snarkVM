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
use snarkvm_circuits::{Boolean as BooleanCircuit, Eject, Environment, Mode};

use nom::{branch::alt, combinator::value};

pub struct Boolean<E: Environment>(BooleanCircuit<E>);

impl<E: Environment> Boolean<E> {
    pub fn new(input: &str) -> ParserResult<Self> {
        // Parse the boolean from the input.
        let (input, boolean) = alt((value(true, keyword("true")), value(false, keyword("false"))))(input)?;
        // Output the remaining input and the initialized boolean.
        Ok((input, Self(BooleanCircuit::new(Mode::Constant, boolean))))
    }

    pub fn to_value(&self) -> bool {
        self.0.eject_value()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits::Circuit;

    #[test]
    fn test_boolean_new() {
        type E = Circuit;
        assert_eq!(true, Boolean::<E>::new("true").unwrap().1.to_value());
        assert_eq!(false, Boolean::<E>::new("false").unwrap().1.to_value());
    }

    #[test]
    fn test_malformed_boolean() {
        type E = Circuit;
        assert!(Boolean::<E>::new("maybe").is_err());
        assert!(Boolean::<E>::new("truee").is_err());
        assert!(Boolean::<E>::new("truefalse").is_err());
        assert!(Boolean::<E>::new("falsetrue").is_err());
    }
}
