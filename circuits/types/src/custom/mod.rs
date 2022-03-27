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

#![forbid(unsafe_code)]

// #[cfg(test)]
// use snarkvm_circuits_environment::assert_scope;

use crate::{Literal, Boolean, StringType};
use snarkvm_circuits_environment::{prelude::*, string_parser::parse_string};
// use snarkvm_utilities::error;

#[derive(Clone)]
pub struct Custom<E: Environment> {
    /// The name of the custom circuit.
    name: StringType<E>,
    /// The inputs of the custom circuit.
    data: Vec<Literal<E>>,
}

// impl<E: Environment> CustomTrait for Custom<E> {}

// impl<E: Environment> Custom<E> {
//     /// Returns the type name of the custom circuit.
//     pub fn type_name(&self) -> &str {
//         &self.name.eject_value()
//     }
// }

// impl<E: Environment> Inject for Custom<E> {
//     type Primitive = (StringType<E>, Vec<Literal<E>>);
//
//     /// Initializes a new instance of a custom circuit.
//     fn new(_mode: Mode, (name, data): Self::Primitive) -> Self {
//         let num_characters = name.len();
//         match num_characters <= E::NUM_IDENTIFIER_CHARS {
//             true => Self { name, data },
//             false => E::halt(format!("Failed to read custom circuit name of length {num_characters}")),
//         }
//     }
// }

// impl<E: Environment> Eject for Custom<E> {
//     type Primitive = (StringType<E>, Vec<Literal<E>>);
//
//     ///
//     /// Ejects the mode of the custom circuit.
//     ///
//     fn eject_mode(&self) -> Mode {
//         self.data.eject_mode()
//     }
//
//     ///
//     /// Ejects the literals of the custom circuit.
//     ///
//     fn eject_value(&self) -> Self::Primitive {
//         (self.name.clone(), self.data.clone())
//     }
// }

// impl<E: Environment> Parser for Custom<E> {
//     type Environment = E;
//
//     /// Parses a string into a custom circuit.
//     #[inline]
//     fn parse(string: &str) -> ParserResult<Self> {
//         // Parse the circuit type name from the string.
//         let (string, name) = map_res(recognize(pair(alpha1, many0(alt((alphanumeric1, tag("_")))))), |name: &str| {
//             let num_characters = name.len();
//             // Note: This is a duplicate check as the parser is a DOS vector.
//             match num_characters <= E::NUM_IDENTIFIER_CHARS {
//                 true => Ok(name),
//                 false => Err(error(format!("Failed to read custom circuit name of length {num_characters}"))),
//             }
//         })(string)?;
//         // Parse the colon ':' keyword from the string.
//         let (string, _) = tag(":")(string)?;
//
//         // Parse the inputs from the string.
//         let (string, inputs) = many0(|s| Input::parse(s, memory.clone()))(string)?;
//         // Parse the instructions from the string.
//         let (string, instructions) = many1(|s| Instruction::parse(s, memory.clone()))(string)?;
//
//         Ok((string, Self::new()))
//     }
// }

// impl<E: Environment> fmt::Debug for Custom<E> {
//     fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
//         let (name, data) = self.eject_value();
//         write!(f, "{} {:?}", name, data)
//     }
// }
//
// impl<E: Environment> fmt::Display for Custom<E> {
//     fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
//         let mut output = format!("{}:\n", self.name.eject_value());
//         for literal in &self.data {
//             output += &format!("    {};", literal);
//         }
//         write!(f, "{}", output)
//     }
// }

impl<E: Environment> ToBits for Custom<E> {
    type Boolean = Boolean<E>;

    /// Returns the little-endian bits of the custom circuit.
    fn to_bits_le(&self) -> Vec<Boolean<E>> {
        self.name.to_bits_le().iter().chain(self.data.to_bits_le().iter()).cloned().collect()
    }

    /// Returns the big-endian bits of the custom circuit.
    fn to_bits_be(&self) -> Vec<Boolean<E>> {
        let mut bits_le = self.to_bits_le();
        bits_le.reverse();
        bits_le
    }
}
