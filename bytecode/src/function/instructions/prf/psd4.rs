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

/// Performs a Poseidon PRF with an input rate of 4.
pub type PRFPsd4<P> = PRF<P, Psd4>;

pub struct Psd4;
impl PRFOpcode for Psd4 {
    const OPCODE: &'static str = "prf.psd4";
}

#[ignore]
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
        let (_, instruction) = Instruction::<P>::parse("prf.psd4 r0 r1 into r2;").unwrap();
        assert!(matches!(instruction, Instruction::PRFPsd4(_)));
    }

    test_modes!(
        address,
        PRFPsd4,
        "1field",
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah",
        "5066783574120618677116553403682103790412182040164919000837548363424948763186field"
    );
    test_modes!(
        bool,
        PRFPsd4,
        "1field",
        "true",
        "6229756969264115413585263939951543289388259445046242982885385276831834290443field"
    );
    test_modes!(
        field,
        PRFPsd4,
        "1field",
        "1field",
        "6229756969264115413585263939951543289388259445046242982885385276831834290443field"
    );
    test_modes!(
        group,
        PRFPsd4,
        "1field",
        "2group",
        "1593416550329010846351876877858675905640984310245243217021847343379621836065field"
    );
    test_modes!(
        i8,
        PRFPsd4,
        "1field",
        "1i8",
        "6229756969264115413585263939951543289388259445046242982885385276831834290443field"
    );
    test_modes!(
        i16,
        PRFPsd4,
        "1field",
        "1i16",
        "6229756969264115413585263939951543289388259445046242982885385276831834290443field"
    );
    test_modes!(
        i32,
        PRFPsd4,
        "1field",
        "1i32",
        "6229756969264115413585263939951543289388259445046242982885385276831834290443field"
    );
    test_modes!(
        i64,
        PRFPsd4,
        "1field",
        "1i64",
        "6229756969264115413585263939951543289388259445046242982885385276831834290443field"
    );
    test_modes!(
        i128,
        PRFPsd4,
        "1field",
        "1i128",
        "6229756969264115413585263939951543289388259445046242982885385276831834290443field"
    );
    test_modes!(
        u8,
        PRFPsd4,
        "1field",
        "1u8",
        "6229756969264115413585263939951543289388259445046242982885385276831834290443field"
    );
    test_modes!(
        u16,
        PRFPsd4,
        "1field",
        "1u16",
        "6229756969264115413585263939951543289388259445046242982885385276831834290443field"
    );
    test_modes!(
        u32,
        PRFPsd4,
        "1field",
        "1u32",
        "6229756969264115413585263939951543289388259445046242982885385276831834290443field"
    );
    test_modes!(
        u64,
        PRFPsd4,
        "1field",
        "1u64",
        "6229756969264115413585263939951543289388259445046242982885385276831834290443field"
    );
    test_modes!(
        u128,
        PRFPsd4,
        "1field",
        "1u128",
        "6229756969264115413585263939951543289388259445046242982885385276831834290443field"
    );
    test_modes!(
        scalar,
        PRFPsd4,
        "1field",
        "1scalar",
        "6229756969264115413585263939951543289388259445046242982885385276831834290443field"
    );
    test_modes!(
        string,
        PRFPsd4,
        "1field",
        "\"aaaaaaaa\"",
        "2174378004607549766027966692552636329925521539782036605523332944372487782805field"
    );

    test_instruction_halts!(
        wrong_seed,
        PRFPsd4,
        "Invalid seed type for PRF, expected a field element",
        "1scalar",
        "1u8"
    );

    #[test]
    fn test_definition() {
        let first = Value::from_str("1field.private");
        let second = Value::<P>::Definition(Identifier::from_str("message"), vec![
            Value::from_str("1field.public"),
            Value::from_str("2field.private"),
        ]);

        let registers = Registers::<P>::default();
        registers.define(&Register::from_str("r0"));
        registers.define(&Register::from_str("r1"));
        registers.define(&Register::from_str("r2"));
        registers.assign(&Register::from_str("r0"), first);
        registers.assign(&Register::from_str("r1"), second);

        PRFPsd4::from_str("r0 r1 into r2").evaluate(&registers);

        let value = registers.load(&Register::from_str("r2"));
        let expected = Value::<P>::from_str(
            "1317849991000100466415733456243419358347804358763027182424593882556510238777field.private",
        );
        assert_eq!(expected, value);
    }
}
