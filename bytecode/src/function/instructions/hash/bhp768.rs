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

/// Performs a BHP hash taking up to a 768-bit value as input.
pub type HashBHP768<P> = Hash<P, BHP768>;

pub struct BHP768;
impl HashOpcode for BHP768 {
    const OPCODE: &'static str = "hash.bhp768";
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

    #[test]
    fn test_parse() {
        let (_, instruction) = Instruction::<P>::parse("hash.bhp768 r0 into r1;").unwrap();
        assert!(matches!(instruction, Instruction::HashBHP768(_)));
    }

    test_modes!(
        address,
        HashBHP768,
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah",
        "7733626634617628833843016991394948005986099438558958305753366472825030371456field"
    );
    test_modes!(
        field,
        HashBHP768,
        "1field",
        "4043812796897213646258524535134835140854558949612693725617655625199315170090field"
    );
    test_modes!(
        group,
        HashBHP768,
        "2group",
        "78810629918916926520436895999768888967344688051772389928455704029852143523field"
    );
    test_modes!(
        scalar,
        HashBHP768,
        "1scalar",
        "6819641070929141541542313329184555049025987364095020651525894363086985689463field"
    );
    test_modes!(
        string,
        HashBHP768,
        "\"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\"",
        "1337805847064924189360346679648564025097815686390893296766092279271614711400field"
    );

    test_instruction_halts!(bool_halts, HashBHP768, "Inputs to this BHP variant must be greater than 129 bits", "true");
    test_instruction_halts!(i8_halts, HashBHP768, "Inputs to this BHP variant must be greater than 129 bits", "1i8");
    test_instruction_halts!(i16_halts, HashBHP768, "Inputs to this BHP variant must be greater than 129 bits", "1i16");
    test_instruction_halts!(i32_halts, HashBHP768, "Inputs to this BHP variant must be greater than 129 bits", "1i32");
    test_instruction_halts!(i64_halts, HashBHP768, "Inputs to this BHP variant must be greater than 129 bits", "1i64");
    test_instruction_halts!(
        i128_halts,
        HashBHP768,
        "Inputs to this BHP variant must be greater than 129 bits",
        "1i128"
    );
    test_instruction_halts!(u8_halts, HashBHP768, "Inputs to this BHP variant must be greater than 129 bits", "1u8");
    test_instruction_halts!(u16_halts, HashBHP768, "Inputs to this BHP variant must be greater than 129 bits", "1u16");
    test_instruction_halts!(u32_halts, HashBHP768, "Inputs to this BHP variant must be greater than 129 bits", "1u32");
    test_instruction_halts!(u64_halts, HashBHP768, "Inputs to this BHP variant must be greater than 129 bits", "1u64");
    test_instruction_halts!(
        u128_halts,
        HashBHP768,
        "Inputs to this BHP variant must be greater than 129 bits",
        "1u128"
    );
    test_instruction_halts!(
        string_halts,
        HashBHP768,
        "Inputs to this BHP variant cannot exceed 774 bits",
        "\"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\""
    );

    #[test]
    fn test_definition() {
        let first = Value::<P>::Definition(Identifier::from_str("message"), vec![
            Value::from_str("1field.public"),
            Value::from_str("false.private"),
        ]);

        let registers = Registers::<P>::default();
        registers.define(&Register::from_str("r0"));
        registers.define(&Register::from_str("r1"));
        registers.assign(&Register::from_str("r0"), first);

        HashBHP768::from_str("r0 into r1").evaluate(&registers);

        let value = registers.load(&Register::from_str("r1"));
        let expected = Value::<P>::from_str(
            "6355776076362174466174411260932929223337545693271706659341750565908781698204field.private",
        );
        assert_eq!(expected, value);
    }

    #[test]
    #[should_panic(expected = "Inputs to this BHP variant cannot exceed 774 bits")]
    fn test_definition_halts() {
        let first = Value::<P>::Definition(Identifier::from_str("message"), vec![
            Value::from_str("1field.public"),
            Value::from_str("2field.private"),
            Value::from_str("3field.private"),
        ]);

        let registers = Registers::<P>::default();
        registers.define(&Register::from_str("r0"));
        registers.define(&Register::from_str("r1"));
        registers.assign(&Register::from_str("r0"), first);

        HashBHP768::from_str("r0 into r1").evaluate(&registers);
    }
}
