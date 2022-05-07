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

/// Performs a Pedersen hash taking up to a 1024-bit value as input.
pub type HashPed1024<P> = Hash<P, Ped1024>;

pub struct Ped1024;
impl HashOpcode for Ped1024 {
    const OPCODE: &'static str = "hash.ped1024";
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        function::{Instruction, Operation, Registers},
        test_instruction_halts,
        test_modes,
        Identifier,
        Process,
        Register,
        Value,
    };
    use snarkvm_circuits::{Literal, Parser};

    type P = Process;

    #[test]
    fn test_parse() {
        let (_, instruction) = Instruction::<P>::parse("hash.ped1024 r0 into r1;").unwrap();
        assert!(matches!(instruction, Instruction::HashPed1024(_)));
    }

    test_modes!(
        address,
        HashPed1024,
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah",
        "4826963288406528492044154107851754184430210982621861457438139969816588083927field"
    );
    test_modes!(
        bool,
        HashPed1024,
        "true",
        "4371866667159521773926408611422706398474622567079831354977654311841624512127field"
    );
    test_modes!(
        field,
        HashPed1024,
        "1field",
        "4371866667159521773926408611422706398474622567079831354977654311841624512127field"
    );
    test_modes!(
        group,
        HashPed1024,
        "2group",
        "597585531527000868040372017246561746942294520454127027945459231174928334857field"
    );
    test_modes!(
        i8,
        HashPed1024,
        "1i8",
        "4371866667159521773926408611422706398474622567079831354977654311841624512127field"
    );
    test_modes!(
        i16,
        HashPed1024,
        "1i16",
        "4371866667159521773926408611422706398474622567079831354977654311841624512127field"
    );
    test_modes!(
        i32,
        HashPed1024,
        "1i32",
        "4371866667159521773926408611422706398474622567079831354977654311841624512127field"
    );
    test_modes!(
        i64,
        HashPed1024,
        "1i64",
        "4371866667159521773926408611422706398474622567079831354977654311841624512127field"
    );
    test_modes!(
        i128,
        HashPed1024,
        "1i128",
        "4371866667159521773926408611422706398474622567079831354977654311841624512127field"
    );
    test_modes!(
        u8,
        HashPed1024,
        "1u8",
        "4371866667159521773926408611422706398474622567079831354977654311841624512127field"
    );
    test_modes!(
        u16,
        HashPed1024,
        "1u16",
        "4371866667159521773926408611422706398474622567079831354977654311841624512127field"
    );
    test_modes!(
        u32,
        HashPed1024,
        "1u32",
        "4371866667159521773926408611422706398474622567079831354977654311841624512127field"
    );
    test_modes!(
        u64,
        HashPed1024,
        "1u64",
        "4371866667159521773926408611422706398474622567079831354977654311841624512127field"
    );
    test_modes!(
        u128,
        HashPed1024,
        "1u128",
        "4371866667159521773926408611422706398474622567079831354977654311841624512127field"
    );
    test_modes!(
        scalar,
        HashPed1024,
        "1scalar",
        "4371866667159521773926408611422706398474622567079831354977654311841624512127field"
    );
    test_modes!(
        string,
        HashPed1024,
        "\"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\"",
        "6130622140007907217618549322433758059283145236233313981773213613980080089179field"
    );

    test_instruction_halts!(
        string_halts,
        HashPed1024,
        "The Pedersen hash input cannot exceed 1024 bits.",
        "\"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\""
    );

    #[test]
    fn test_definition() {
        let first = Value::<P>::Definition(Identifier::from_str("message"), vec![
            Literal::from_str("true.public"),
            Literal::from_str("false.private"),
        ]);

        let registers = Registers::<P>::default();
        registers.define(&Register::from_str("r0"));
        registers.define(&Register::from_str("r1"));
        registers.assign(&Register::from_str("r0"), first);

        HashPed1024::from_str("r0 into r1").evaluate(&registers);

        let value = registers.load(&Register::from_str("r1"));
        let expected = Value::<P>::from_str(
            "4371866667159521773926408611422706398474622567079831354977654311841624512127field.private",
        );
        assert_eq!(expected, value);
    }

    #[test]
    #[should_panic(expected = "The Pedersen hash input cannot exceed 1024 bits.")]
    fn test_definition_halts() {
        let first = Value::<P>::Definition(Identifier::from_str("message"), vec![
            Literal::from_str("1field.public"),
            Literal::from_str("2field.private"),
            Literal::from_str("3field.private"),
            Literal::from_str("4field.private"),
            Literal::from_str("5field.private"),
        ]);

        let registers = Registers::<P>::default();
        registers.define(&Register::from_str("r0"));
        registers.define(&Register::from_str("r1"));
        registers.assign(&Register::from_str("r0"), first);

        HashPed1024::from_str("r0 into r1").evaluate(&registers);
    }
}
