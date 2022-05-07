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

/// Performs a Poseidon PRF with an input rate of 2.
pub type PRFPsd2<P> = PRF<P, Psd2>;

pub struct Psd2;
impl PRFOpcode for Psd2 {
    const OPCODE: &'static str = "prf.psd2";
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
        let (_, instruction) = Instruction::<P>::parse("prf.psd2 r0 r1 into r2;").unwrap();
        assert!(matches!(instruction, Instruction::PRFPsd2(_)));
    }

    test_modes!(
        address,
        PRFPsd2,
        "1field",
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah",
        "5429059144042855058903165151470094608574718063754624535304095716521206205979field"
    );
    test_modes!(
        bool,
        PRFPsd2,
        "1field",
        "true",
        "264064256139711157964411468768199659744432155768657473206504630824077396812field"
    );
    test_modes!(
        field,
        PRFPsd2,
        "1field",
        "1field",
        "264064256139711157964411468768199659744432155768657473206504630824077396812field"
    );
    test_modes!(
        group,
        PRFPsd2,
        "1field",
        "2group",
        "1224211494388177159455761886435012160305812121348005682846231180844190427793field"
    );
    test_modes!(
        i8,
        PRFPsd2,
        "1field",
        "1i8",
        "264064256139711157964411468768199659744432155768657473206504630824077396812field"
    );
    test_modes!(
        i16,
        PRFPsd2,
        "1field",
        "1i16",
        "264064256139711157964411468768199659744432155768657473206504630824077396812field"
    );
    test_modes!(
        i32,
        PRFPsd2,
        "1field",
        "1i32",
        "264064256139711157964411468768199659744432155768657473206504630824077396812field"
    );
    test_modes!(
        i64,
        PRFPsd2,
        "1field",
        "1i64",
        "264064256139711157964411468768199659744432155768657473206504630824077396812field"
    );
    test_modes!(
        i128,
        PRFPsd2,
        "1field",
        "1i128",
        "264064256139711157964411468768199659744432155768657473206504630824077396812field"
    );
    test_modes!(
        u8,
        PRFPsd2,
        "1field",
        "1u8",
        "264064256139711157964411468768199659744432155768657473206504630824077396812field"
    );
    test_modes!(
        u16,
        PRFPsd2,
        "1field",
        "1u16",
        "264064256139711157964411468768199659744432155768657473206504630824077396812field"
    );
    test_modes!(
        u32,
        PRFPsd2,
        "1field",
        "1u32",
        "264064256139711157964411468768199659744432155768657473206504630824077396812field"
    );
    test_modes!(
        u64,
        PRFPsd2,
        "1field",
        "1u64",
        "264064256139711157964411468768199659744432155768657473206504630824077396812field"
    );
    test_modes!(
        u128,
        PRFPsd2,
        "1field",
        "1u128",
        "264064256139711157964411468768199659744432155768657473206504630824077396812field"
    );
    test_modes!(
        scalar,
        PRFPsd2,
        "1field",
        "1scalar",
        "264064256139711157964411468768199659744432155768657473206504630824077396812field"
    );
    test_modes!(
        string,
        PRFPsd2,
        "1field",
        "\"aaaaaaaa\"",
        "4045898559514852959305269527680718487035688384207023382886187634629104660887field"
    );

    test_instruction_halts!(
        wrong_seed,
        PRFPsd2,
        "Unreachable literal variant detected during PRF calculation.",
        "1scalar",
        "1u8"
    );

    #[test]
    fn test_definition() {
        let first = Literal::from_str("1field.private");
        let second = Value::<P>::Definition(Identifier::from_str("message"), vec![
            Literal::from_str("1field.public"),
            Literal::from_str("2field.private"),
        ]);

        let registers = Registers::<P>::default();
        registers.define(&Register::from_str("r0"));
        registers.define(&Register::from_str("r1"));
        registers.define(&Register::from_str("r2"));
        registers.assign(&Register::from_str("r0"), first);
        registers.assign(&Register::from_str("r1"), second);

        PRFPsd2::from_str("r0 r1 into r2").evaluate(&registers);

        let value = registers.load(&Register::from_str("r2"));
        let expected = Value::<P>::from_str(
            "1229961230903946015049212727085586100476924753751618406815341787923555981521field.private",
        );
        assert_eq!(expected, value);
    }
}
