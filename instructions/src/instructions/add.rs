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

pub enum Add {

}

impl Add {
    pub fn new(input: &str) -> ParserResult<Self> {

    }

    pub fn to_value(&self) -> () {

    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::str::FromStr;

    #[test]
    fn test_add_new() {
        assert_eq!(
            Fq::from_str("5").unwrap(),
            Base::new("5base").unwrap().1.unwrap().to_value()
        );
    }

    #[test]
    fn test_malformed_add() {
        assert!(Base::new("5ba_se").is_err());
    }
}
