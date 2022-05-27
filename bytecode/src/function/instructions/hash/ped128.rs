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

use super::*;

/// Performs a Pedersen hash taking up to a 128-bit value as input.
pub type HashPed128<P> = Hash<P, Ped128>;

pub struct Ped128;
impl HashOpcode for Ped128 {
    const OPCODE: &'static str = "hash.ped128";
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        function::{Instruction, Operation, Register, Registers},
        test_instruction_halts,
        test_modes,
        Identifier,
        Process,
        Value,
    };
    use snarkvm_circuits::Parser;

    type P = Process;

    #[ignore]
    #[test]
    fn test_parse() {
        let (_, instruction) = Instruction::<P>::parse("hash.ped128 r0 into r1;").unwrap();
        assert!(matches!(instruction, Instruction::HashPed128(_)));
    }

    test_modes!(
        bool,
        HashPed128,
        "true",
        "3598567907039588809097399097576364274194519144238043207544759989534523723417field"
    );
    test_modes!(
        i8,
        HashPed128,
        "1i8",
        "3598567907039588809097399097576364274194519144238043207544759989534523723417field"
    );
    test_modes!(
        i16,
        HashPed128,
        "1i16",
        "3598567907039588809097399097576364274194519144238043207544759989534523723417field"
    );
    test_modes!(
        i32,
        HashPed128,
        "1i32",
        "3598567907039588809097399097576364274194519144238043207544759989534523723417field"
    );
    test_modes!(
        i64,
        HashPed128,
        "1i64",
        "3598567907039588809097399097576364274194519144238043207544759989534523723417field"
    );
    test_modes!(
        i128,
        HashPed128,
        "1i128",
        "3598567907039588809097399097576364274194519144238043207544759989534523723417field"
    );
    test_modes!(
        u8,
        HashPed128,
        "1u8",
        "3598567907039588809097399097576364274194519144238043207544759989534523723417field"
    );
    test_modes!(
        u16,
        HashPed128,
        "1u16",
        "3598567907039588809097399097576364274194519144238043207544759989534523723417field"
    );
    test_modes!(
        u32,
        HashPed128,
        "1u32",
        "3598567907039588809097399097576364274194519144238043207544759989534523723417field"
    );
    test_modes!(
        u64,
        HashPed128,
        "1u64",
        "3598567907039588809097399097576364274194519144238043207544759989534523723417field"
    );
    test_modes!(
        u128,
        HashPed128,
        "1u128",
        "3598567907039588809097399097576364274194519144238043207544759989534523723417field"
    );
    test_modes!(
        string,
        HashPed128,
        "\"aaaaaaaaaaaaaaaa\"",
        "3418245999097014328039870510007368005669789012142975756708428585921244174966field"
    );

    test_instruction_halts!(
        address_halts,
        HashPed128,
        "The Pedersen hash input cannot exceed 128 bits.",
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah"
    );
    test_instruction_halts!(field_halts, HashPed128, "The Pedersen hash input cannot exceed 128 bits.", "1field");
    test_instruction_halts!(group_halts, HashPed128, "The Pedersen hash input cannot exceed 128 bits.", "2group");
    test_instruction_halts!(scalar_halts, HashPed128, "The Pedersen hash input cannot exceed 128 bits.", "1scalar");
    test_instruction_halts!(
        string_halts,
        HashPed128,
        "The Pedersen hash input cannot exceed 128 bits.",
        "\"aaaaaaaaaaaaaaaaaa\""
    );

    #[ignore]
    #[test]
    fn test_definition() {
        let first = Value::<P>::Definition(Identifier::from_str("message"), vec![
            Value::from_str("true.public"),
            Value::from_str("false.private"),
        ]);

        let registers = Registers::<P>::default();
        registers.define(&Register::from_str("r0"));
        registers.define(&Register::from_str("r1"));
        registers.assign(&Register::from_str("r0"), first);

        HashPed128::from_str("r0 into r1").evaluate(&registers);

        let value = registers.load(&Register::from_str("r1"));
        let expected = Value::<P>::from_str(
            "1982792668379688029986293889617072121975206704774322859103778761030904565836field.private",
        );
        assert_eq!(expected, value);
    }

    #[ignore]
    #[test]
    #[should_panic(expected = "The Pedersen hash input cannot exceed 128 bits.")]
    fn test_definition_halts() {
        let first = Value::<P>::Definition(Identifier::from_str("message"), vec![
            Value::from_str("1field.public"),
            Value::from_str("false.private"),
        ]);

        let registers = Registers::<P>::default();
        registers.define(&Register::from_str("r0"));
        registers.define(&Register::from_str("r1"));
        registers.assign(&Register::from_str("r0"), first);

        HashPed128::from_str("r0 into r1").evaluate(&registers);
    }
}
