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

use snarkvm_bytecode::{Function, Immediate, Memory, Stack};
use snarkvm_circuits::{traits::*, Circuit};

pub struct HelloWorld;

impl HelloWorld {
    /// Initializes a new instance of `HelloWorld` with the given inputs.
    pub fn run<M: Memory>(inputs: [Immediate<M::Environment>; 2]) -> Vec<Immediate<M::Environment>> {
        Function::<M>::from_str(
            r"
function main:
    input r0 field.public;
    input r1 field.private;
    add r2 r0 r1;
    output r2 field.private;
",
        )
        .evaluate(&inputs)
    }
}

fn main() {
    let first = Immediate::from_str("1field.public");
    let second = Immediate::from_str("1field.private");

    let expected = Immediate::from_str("2field.private");
    let candidate = HelloWorld::run::<Stack<Circuit>>([first, second]);

    match (&expected, &candidate[0]) {
        (Immediate::Field(expected), Immediate::Field(candidate)) => {
            println!("{candidate}");
            assert!(expected.is_eq(candidate).eject_value());
        }
        _ => panic!("Failed to load output"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_utilities::{FromBytes, ToBytes};

    #[test]
    fn test_hello_world() {
        let first = Immediate::from_str("1field.public");
        let second = Immediate::from_str("1field.private");

        let expected = Immediate::from_str("2field.private");
        let candidate = HelloWorld::run::<Stack<Circuit>>([first, second]);

        match (&expected, &candidate[0]) {
            (Immediate::Field(expected), Immediate::Field(candidate)) => {
                assert!(expected.is_eq(candidate).eject_value())
            }
            _ => panic!("Failed to load output"),
        }
    }

    #[test]
    fn test_to_and_from_bytes() {
        type M = Stack<Circuit>;
        let function_string = r"
function main:
    input r0 field.public;
    input r1 field.private;
    add r2 r0 r1;
    add r3 r0 r1;
    add r4 r0 r1;
    add r5 r0 r1;
    add r6 r0 r1;
    add r7 r0 r1;
    add r8 r0 r1;
    add r9 r0 r1;
    add r10 r0 r1;
    add r11 r0 r1;
    output r2 field.private;
";
        let function_from_string = Function::<M>::from_str(function_string);
        let bytes = function_from_string.to_bytes_le().unwrap();

        println!("String size: {:?}, Bytecode size: {:?}", function_string.as_bytes().len(), bytes.len());

        Function::<M>::from_bytes_le(&bytes).unwrap();
    }
}
