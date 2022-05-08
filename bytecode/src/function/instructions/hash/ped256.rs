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

/// Performs a Pedersen hash taking up to a 256-bit value as input.
pub type HashPed256<P> = Hash<P, Ped256>;

pub struct Ped256;
impl HashOpcode for Ped256 {
    const OPCODE: &'static str = "hash.ped256";
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
        let (_, instruction) = Instruction::<P>::parse("hash.ped256 r0 into r1;").unwrap();
        assert!(matches!(instruction, Instruction::HashPed256(_)));
    }

    test_modes!(
        address,
        HashPed256,
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah",
        "1707603226242263638396158295735486432029534862886227306527076739649781792635field"
    );
    test_modes!(
        bool,
        HashPed256,
        "true",
        "6862094408223630346583350103044196166214351587854542536995775123438608534373field"
    );
    test_modes!(
        field,
        HashPed256,
        "1field",
        "6862094408223630346583350103044196166214351587854542536995775123438608534373field"
    );
    test_modes!(
        group,
        HashPed256,
        "2group",
        "6164722171185479197648832471229106165210044152108402435467195089571507562479field"
    );
    test_modes!(
        i8,
        HashPed256,
        "1i8",
        "6862094408223630346583350103044196166214351587854542536995775123438608534373field"
    );
    test_modes!(
        i16,
        HashPed256,
        "1i16",
        "6862094408223630346583350103044196166214351587854542536995775123438608534373field"
    );
    test_modes!(
        i32,
        HashPed256,
        "1i32",
        "6862094408223630346583350103044196166214351587854542536995775123438608534373field"
    );
    test_modes!(
        i64,
        HashPed256,
        "1i64",
        "6862094408223630346583350103044196166214351587854542536995775123438608534373field"
    );
    test_modes!(
        i128,
        HashPed256,
        "1i128",
        "6862094408223630346583350103044196166214351587854542536995775123438608534373field"
    );
    test_modes!(
        u8,
        HashPed256,
        "1u8",
        "6862094408223630346583350103044196166214351587854542536995775123438608534373field"
    );
    test_modes!(
        u16,
        HashPed256,
        "1u16",
        "6862094408223630346583350103044196166214351587854542536995775123438608534373field"
    );
    test_modes!(
        u32,
        HashPed256,
        "1u32",
        "6862094408223630346583350103044196166214351587854542536995775123438608534373field"
    );
    test_modes!(
        u64,
        HashPed256,
        "1u64",
        "6862094408223630346583350103044196166214351587854542536995775123438608534373field"
    );
    test_modes!(
        u128,
        HashPed256,
        "1u128",
        "6862094408223630346583350103044196166214351587854542536995775123438608534373field"
    );
    test_modes!(
        scalar,
        HashPed256,
        "1scalar",
        "6862094408223630346583350103044196166214351587854542536995775123438608534373field"
    );
    test_modes!(
        string,
        HashPed256,
        "\"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\"",
        "6652850389942784994570468815885188300219232101024755094784397062543323126547field"
    );

    test_instruction_halts!(
        string_halts,
        HashPed256,
        "The Pedersen hash input cannot exceed 256 bits.",
        "\"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\""
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

        HashPed256::from_str("r0 into r1").evaluate(&registers);

        let value = registers.load(&Register::from_str("r1"));
        let expected = Value::<P>::from_str(
            "2507336238525241920229363127502836554394792067069106023108137013905810817541field.private",
        );
        assert_eq!(expected, value);
    }

    #[test]
    #[should_panic(expected = "The Pedersen hash input cannot exceed 256 bits.")]
    fn test_definition_halts() {
        let first = Value::<P>::Definition(Identifier::from_str("message"), vec![
            Literal::from_str("1field.public").into(),
            Literal::from_str("2field.private").into(),
        ]);

        let registers = Registers::<P>::default();
        registers.define(&Register::from_str("r0"));
        registers.define(&Register::from_str("r1"));
        registers.assign(&Register::from_str("r0"), first);

        HashPed256::from_str("r0 into r1").evaluate(&registers);
    }
}
