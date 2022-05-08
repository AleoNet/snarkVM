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

/// Performs a Pedersen hash taking up to a 512-bit value as input.
pub type HashPed512<P> = Hash<P, Ped512>;

pub struct Ped512;
impl HashOpcode for Ped512 {
    const OPCODE: &'static str = "hash.ped512";
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
    use snarkvm_circuits::{Literal, Parser};

    type P = Process;

    #[test]
    fn test_parse() {
        let (_, instruction) = Instruction::<P>::parse("hash.ped512 r0 into r1;").unwrap();
        assert!(matches!(instruction, Instruction::HashPed512(_)));
    }

    test_modes!(
        address,
        HashPed512,
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah",
        "351949238953146061747566525133127056474991555945454616183135808470063265817field"
    );
    test_modes!(
        bool,
        HashPed512,
        "true",
        "5977699428735859836057783079829767840487485526717429264425888196253596787835field"
    );
    test_modes!(
        field,
        HashPed512,
        "1field",
        "5977699428735859836057783079829767840487485526717429264425888196253596787835field"
    );
    test_modes!(
        group,
        HashPed512,
        "2group",
        "7373209553664976434828985470249421537529730063340011739151811610236976669332field"
    );
    test_modes!(
        i8,
        HashPed512,
        "1i8",
        "5977699428735859836057783079829767840487485526717429264425888196253596787835field"
    );
    test_modes!(
        i16,
        HashPed512,
        "1i16",
        "5977699428735859836057783079829767840487485526717429264425888196253596787835field"
    );
    test_modes!(
        i32,
        HashPed512,
        "1i32",
        "5977699428735859836057783079829767840487485526717429264425888196253596787835field"
    );
    test_modes!(
        i64,
        HashPed512,
        "1i64",
        "5977699428735859836057783079829767840487485526717429264425888196253596787835field"
    );
    test_modes!(
        i128,
        HashPed512,
        "1i128",
        "5977699428735859836057783079829767840487485526717429264425888196253596787835field"
    );
    test_modes!(
        u8,
        HashPed512,
        "1u8",
        "5977699428735859836057783079829767840487485526717429264425888196253596787835field"
    );
    test_modes!(
        u16,
        HashPed512,
        "1u16",
        "5977699428735859836057783079829767840487485526717429264425888196253596787835field"
    );
    test_modes!(
        u32,
        HashPed512,
        "1u32",
        "5977699428735859836057783079829767840487485526717429264425888196253596787835field"
    );
    test_modes!(
        u64,
        HashPed512,
        "1u64",
        "5977699428735859836057783079829767840487485526717429264425888196253596787835field"
    );
    test_modes!(
        u128,
        HashPed512,
        "1u128",
        "5977699428735859836057783079829767840487485526717429264425888196253596787835field"
    );
    test_modes!(
        scalar,
        HashPed512,
        "1scalar",
        "5977699428735859836057783079829767840487485526717429264425888196253596787835field"
    );
    test_modes!(
        string,
        HashPed512,
        "\"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\"",
        "4351455226561643062226174077344187779285717251260828583278457676706800691855field"
    );

    test_instruction_halts!(
        string_halts,
        HashPed512,
        "The Pedersen hash input cannot exceed 512 bits.",
        "\"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\""
    );

    #[test]
    fn test_definition() {
        let first = Value::<P>::Definition(Identifier::from_str("message"), vec![
            Literal::from_str("true.public").into(),
            Literal::from_str("false.private").into(),
        ]);

        let registers = Registers::<P>::default();
        registers.define(&Register::from_str("r0"));
        registers.define(&Register::from_str("r1"));
        registers.assign(&Register::from_str("r0"), first);

        HashPed512::from_str("r0 into r1").evaluate(&registers);

        let value = registers.load(&Register::from_str("r1"));
        let expected = Value::<P>::from_str(
            "7049665342751840770504795488969963304104382420108967807703906789591411328969field.private",
        );
        assert_eq!(expected, value);
    }

    #[test]
    #[should_panic(expected = "The Pedersen hash input cannot exceed 512 bits.")]
    fn test_definition_halts() {
        let first = Value::<P>::Definition(Identifier::from_str("message"), vec![
            Literal::from_str("1field.public").into(),
            Literal::from_str("2field.private").into(),
            Literal::from_str("3field.private").into(),
        ]);

        let registers = Registers::<P>::default();
        registers.define(&Register::from_str("r0"));
        registers.define(&Register::from_str("r1"));
        registers.assign(&Register::from_str("r0"), first);

        HashPed512::from_str("r0 into r1").evaluate(&registers);
    }
}
