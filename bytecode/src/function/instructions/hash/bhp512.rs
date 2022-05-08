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

/// Performs a BHP hash taking up to a 512-bit value as input.
pub type HashBHP512<P> = Hash<P, BHP512>;

pub struct BHP512;
impl HashOpcode for BHP512 {
    const OPCODE: &'static str = "hash.bhp512";
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
        let (_, instruction) = Instruction::<P>::parse("hash.bhp512 r0 into r1;").unwrap();
        assert!(matches!(instruction, Instruction::HashBHP512(_)));
    }

    test_modes!(
        address,
        HashBHP512,
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah",
        "2332379726510100270911348833755760534031231986206113558327744059876100043583field"
    );
    test_modes!(
        field,
        HashBHP512,
        "1field",
        "7859505366134605419571079611358314299378384003680687055919221906144872990437field"
    );
    test_modes!(
        group,
        HashBHP512,
        "2group",
        "1206169886314558320468283062252027416231715323849381455759457424983927569134field"
    );
    test_modes!(
        scalar,
        HashBHP512,
        "1scalar",
        "2589905780188216451634860187962040500314156773894129398705695803874231317852field"
    );
    test_modes!(
        string,
        HashBHP512,
        "\"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\"",
        "6561516010343954837160224390550746796779739646280178729144093180258573104330field"
    );

    test_instruction_halts!(bool_halts, HashBHP512, "Inputs to this BHP variant must be greater than 171 bits", "true");
    test_instruction_halts!(i8_halts, HashBHP512, "Inputs to this BHP variant must be greater than 171 bits", "1i8");
    test_instruction_halts!(i16_halts, HashBHP512, "Inputs to this BHP variant must be greater than 171 bits", "1i16");
    test_instruction_halts!(i32_halts, HashBHP512, "Inputs to this BHP variant must be greater than 171 bits", "1i32");
    test_instruction_halts!(i64_halts, HashBHP512, "Inputs to this BHP variant must be greater than 171 bits", "1i64");
    test_instruction_halts!(
        i128_halts,
        HashBHP512,
        "Inputs to this BHP variant must be greater than 171 bits",
        "1i128"
    );
    test_instruction_halts!(u8_halts, HashBHP512, "Inputs to this BHP variant must be greater than 171 bits", "1u8");
    test_instruction_halts!(u16_halts, HashBHP512, "Inputs to this BHP variant must be greater than 171 bits", "1u16");
    test_instruction_halts!(u32_halts, HashBHP512, "Inputs to this BHP variant must be greater than 171 bits", "1u32");
    test_instruction_halts!(u64_halts, HashBHP512, "Inputs to this BHP variant must be greater than 171 bits", "1u64");
    test_instruction_halts!(
        u128_halts,
        HashBHP512,
        "Inputs to this BHP variant must be greater than 171 bits",
        "1u128"
    );
    test_instruction_halts!(
        string_halts,
        HashBHP512,
        "Inputs to this BHP variant cannot exceed 513 bits",
        "\"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\""
    );

    #[test]
    fn test_definition() {
        let first = Value::<P>::Definition(Identifier::from_str("message"), vec![
            Literal::from_str("1field.public"),
            Literal::from_str("false.private"),
        ]);

        let registers = Registers::<P>::default();
        registers.define(&Register::from_str("r0"));
        registers.define(&Register::from_str("r1"));
        registers.assign(&Register::from_str("r0"), first);

        HashBHP512::from_str("r0 into r1").evaluate(&registers);

        let value = registers.load(&Register::from_str("r1"));
        let expected = Value::<P>::from_str(
            "7859505366134605419571079611358314299378384003680687055919221906144872990437field.private",
        );
        assert_eq!(expected, value);
    }

    #[test]
    #[should_panic(expected = "Inputs to this BHP variant cannot exceed 513 bits")]
    fn test_definition_halts() {
        let first = Value::<P>::Definition(Identifier::from_str("message"), vec![
            Literal::from_str("1field.public"),
            Literal::from_str("2field.private"),
            Literal::from_str("3field.private"),
        ]);

        let registers = Registers::<P>::default();
        registers.define(&Register::from_str("r0"));
        registers.define(&Register::from_str("r1"));
        registers.assign(&Register::from_str("r0"), first);

        HashBHP512::from_str("r0 into r1").evaluate(&registers);
    }
}
