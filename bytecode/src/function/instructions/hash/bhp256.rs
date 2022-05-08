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

/// Performs a BHP hash taking up to a 256-bit value as input.
pub type HashBHP256<P> = Hash<P, BHP256>;

pub struct BHP256;
impl HashOpcode for BHP256 {
    const OPCODE: &'static str = "hash.bhp256";
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
        let (_, instruction) = Instruction::<P>::parse("hash.bhp256 r0 into r1;").unwrap();
        assert!(matches!(instruction, Instruction::HashBHP256(_)));
    }

    test_modes!(
        address,
        HashBHP256,
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah",
        "7771681749746338318293997474424175385090931257265731857822357785268749547177field"
    );
    test_modes!(
        field,
        HashBHP256,
        "1field",
        "5874813848001078825440680779117810045498377650622376861960096391249691315761field"
    );
    test_modes!(
        group,
        HashBHP256,
        "2group",
        "7795182442461796707201045295459477745420360285590422302138185253353288555218field"
    );
    test_modes!(
        scalar,
        HashBHP256,
        "1scalar",
        "1797359377483146164045932202987205174809918311940774669490806227922658992682field"
    );
    test_modes!(
        string,
        HashBHP256,
        "\"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\"",
        "592791993572506322612322757869541781863591071410767047170707960751243737584field"
    );

    test_instruction_halts!(bool_halts, HashBHP256, "Inputs to this BHP variant must be greater than 129 bits", "true");
    test_instruction_halts!(i8_halts, HashBHP256, "Inputs to this BHP variant must be greater than 129 bits", "1i8");
    test_instruction_halts!(i16_halts, HashBHP256, "Inputs to this BHP variant must be greater than 129 bits", "1i16");
    test_instruction_halts!(i32_halts, HashBHP256, "Inputs to this BHP variant must be greater than 129 bits", "1i32");
    test_instruction_halts!(i64_halts, HashBHP256, "Inputs to this BHP variant must be greater than 129 bits", "1i64");
    test_instruction_halts!(
        i128_halts,
        HashBHP256,
        "Inputs to this BHP variant must be greater than 129 bits",
        "1i128"
    );
    test_instruction_halts!(u8_halts, HashBHP256, "Inputs to this BHP variant must be greater than 129 bits", "1u8");
    test_instruction_halts!(u16_halts, HashBHP256, "Inputs to this BHP variant must be greater than 129 bits", "1u16");
    test_instruction_halts!(u32_halts, HashBHP256, "Inputs to this BHP variant must be greater than 129 bits", "1u32");
    test_instruction_halts!(u64_halts, HashBHP256, "Inputs to this BHP variant must be greater than 129 bits", "1u64");
    test_instruction_halts!(
        u128_halts,
        HashBHP256,
        "Inputs to this BHP variant must be greater than 129 bits",
        "1u128"
    );
    test_instruction_halts!(
        string_halts,
        HashBHP256,
        "Inputs to this BHP variant cannot exceed 258 bits",
        "\"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\""
    );

    #[test]
    fn test_definition() {
        let first = Value::<P>::Definition(Identifier::from_str("message"), vec![
            Literal::from_str("1u128.public").into(),
            Literal::from_str("1u8.private").into(),
        ]);

        let registers = Registers::<P>::default();
        registers.define(&Register::from_str("r0"));
        registers.define(&Register::from_str("r1"));
        registers.assign(&Register::from_str("r0"), first);

        HashBHP256::from_str("r0 into r1").evaluate(&registers);

        let value = registers.load(&Register::from_str("r1"));
        let expected = Value::<P>::from_str(
            "7037518451104647995701956748302747700592897133164811748578711064244897752727field.private",
        );
        assert_eq!(expected, value);
    }

    #[test]
    #[should_panic(expected = "Inputs to this BHP variant cannot exceed 258 bits")]
    fn test_definition_halts() {
        let first = Value::<P>::Definition(Identifier::from_str("message"), vec![
            Literal::from_str("1field.public").into(),
            Literal::from_str("2field.private").into(),
        ]);

        let registers = Registers::<P>::default();
        registers.define(&Register::from_str("r0"));
        registers.define(&Register::from_str("r1"));
        registers.assign(&Register::from_str("r0"), first);

        HashBHP256::from_str("r0 into r1").evaluate(&registers);
    }
}
