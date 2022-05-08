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

/// Performs a Poseidon hash with an input rate of 2.
pub type HashPsd2<P> = Hash<P, Psd2>;

pub struct Psd2;
impl HashOpcode for Psd2 {
    const OPCODE: &'static str = "hash.psd2";
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        function::{Instruction, Operation, Register, Registers},
        test_modes,
        Identifier,
        Process,
        Value,
    };
    use snarkvm_circuits::{Literal, Parser};

    type P = Process;

    #[test]
    fn test_parse() {
        let (_, instruction) = Instruction::<P>::parse("hash.psd2 r0 into r1;").unwrap();
        assert!(matches!(instruction, Instruction::HashPsd2(_)));
    }

    test_modes!(
        address,
        HashPsd2,
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah",
        "1514568289958193437950521941960970234475890760384450782324072324349892524013field"
    );
    test_modes!(
        bool,
        HashPsd2,
        "true",
        "895920223209807336032370141805192618496779881680412280727415085489332840844field"
    );
    test_modes!(
        field,
        HashPsd2,
        "1field",
        "895920223209807336032370141805192618496779881680412280727415085489332840844field"
    );
    test_modes!(
        group,
        HashPsd2,
        "2group",
        "5683685112813606545476260789417808603439881969054557143180853282078874544349field"
    );
    test_modes!(
        i8,
        HashPsd2,
        "1i8",
        "895920223209807336032370141805192618496779881680412280727415085489332840844field"
    );
    test_modes!(
        i16,
        HashPsd2,
        "1i16",
        "895920223209807336032370141805192618496779881680412280727415085489332840844field"
    );
    test_modes!(
        i32,
        HashPsd2,
        "1i32",
        "895920223209807336032370141805192618496779881680412280727415085489332840844field"
    );
    test_modes!(
        i64,
        HashPsd2,
        "1i64",
        "895920223209807336032370141805192618496779881680412280727415085489332840844field"
    );
    test_modes!(
        i128,
        HashPsd2,
        "1i128",
        "895920223209807336032370141805192618496779881680412280727415085489332840844field"
    );
    test_modes!(
        u8,
        HashPsd2,
        "1u8",
        "895920223209807336032370141805192618496779881680412280727415085489332840844field"
    );
    test_modes!(
        u16,
        HashPsd2,
        "1u16",
        "895920223209807336032370141805192618496779881680412280727415085489332840844field"
    );
    test_modes!(
        u32,
        HashPsd2,
        "1u32",
        "895920223209807336032370141805192618496779881680412280727415085489332840844field"
    );
    test_modes!(
        u64,
        HashPsd2,
        "1u64",
        "895920223209807336032370141805192618496779881680412280727415085489332840844field"
    );
    test_modes!(
        u128,
        HashPsd2,
        "1u128",
        "895920223209807336032370141805192618496779881680412280727415085489332840844field"
    );
    test_modes!(
        scalar,
        HashPsd2,
        "1scalar",
        "895920223209807336032370141805192618496779881680412280727415085489332840844field"
    );
    test_modes!(
        string,
        HashPsd2,
        "\"aaaaaaaa\"",
        "3304929462283992873125391937087251720796648284457823938893125121531366375892field"
    );

    #[test]
    fn test_definition() {
        let first = Value::<P>::Definition(Identifier::from_str("message"), vec![
            Literal::from_str("1field.public").into(),
            Literal::from_str("2field.private").into(),
        ]);

        let registers = Registers::<P>::default();
        registers.define(&Register::from_str("r0"));
        registers.define(&Register::from_str("r1"));
        registers.assign(&Register::from_str("r0"), first);

        HashPsd2::from_str("r0 into r1").evaluate(&registers);

        let value = registers.load(&Register::from_str("r1"));
        let expected = Value::<P>::from_str(
            "8222450193554204153584171334384188568812145149594153017505216002466488233733field.private",
        );
        assert_eq!(expected, value);
    }
}
