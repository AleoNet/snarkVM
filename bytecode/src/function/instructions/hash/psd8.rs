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

/// Performs a Poseidon hash with an input rate of 8.
pub type HashPsd8<P> = Hash<P, Psd8>;

pub struct Psd8;
impl HashOpcode for Psd8 {
    const OPCODE: &'static str = "hash.psd8";
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
        let (_, instruction) = Instruction::<P>::parse("hash.psd8 r0 into r1;").unwrap();
        assert!(matches!(instruction, Instruction::HashPsd8(_)));
    }

    test_modes!(
        address,
        HashPsd8,
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah",
        "7357837442449203764978346428611010139582577962074937408545526785030093239177field"
    );
    test_modes!(
        bool,
        HashPsd8,
        "true",
        "3999071741215241790607111275574824668617854796802626587041088136954841194555field"
    );
    test_modes!(
        field,
        HashPsd8,
        "1field",
        "3999071741215241790607111275574824668617854796802626587041088136954841194555field"
    );
    test_modes!(
        group,
        HashPsd8,
        "2group",
        "6695429252493832541241314081562731262250323832040991237549108911952461806287field"
    );
    test_modes!(
        i8,
        HashPsd8,
        "1i8",
        "3999071741215241790607111275574824668617854796802626587041088136954841194555field"
    );
    test_modes!(
        i16,
        HashPsd8,
        "1i16",
        "3999071741215241790607111275574824668617854796802626587041088136954841194555field"
    );
    test_modes!(
        i32,
        HashPsd8,
        "1i32",
        "3999071741215241790607111275574824668617854796802626587041088136954841194555field"
    );
    test_modes!(
        i64,
        HashPsd8,
        "1i64",
        "3999071741215241790607111275574824668617854796802626587041088136954841194555field"
    );
    test_modes!(
        i128,
        HashPsd8,
        "1i128",
        "3999071741215241790607111275574824668617854796802626587041088136954841194555field"
    );
    test_modes!(
        u8,
        HashPsd8,
        "1u8",
        "3999071741215241790607111275574824668617854796802626587041088136954841194555field"
    );
    test_modes!(
        u16,
        HashPsd8,
        "1u16",
        "3999071741215241790607111275574824668617854796802626587041088136954841194555field"
    );
    test_modes!(
        u32,
        HashPsd8,
        "1u32",
        "3999071741215241790607111275574824668617854796802626587041088136954841194555field"
    );
    test_modes!(
        u64,
        HashPsd8,
        "1u64",
        "3999071741215241790607111275574824668617854796802626587041088136954841194555field"
    );
    test_modes!(
        u128,
        HashPsd8,
        "1u128",
        "3999071741215241790607111275574824668617854796802626587041088136954841194555field"
    );
    test_modes!(
        scalar,
        HashPsd8,
        "1scalar",
        "3999071741215241790607111275574824668617854796802626587041088136954841194555field"
    );
    test_modes!(
        string,
        HashPsd8,
        "\"aaaaaaaa\"",
        "4020837770720319542691472472080405581209506316726251354702740114046129734437field"
    );

    #[test]
    fn test_definition() {
        let first = Value::<P>::Definition(Identifier::from_str("message"), vec![
            Literal::from_str("1field.public"),
            Literal::from_str("2field.private"),
        ]);

        let registers = Registers::<P>::default();
        registers.define(&Register::from_str("r0"));
        registers.define(&Register::from_str("r1"));
        registers.assign(&Register::from_str("r0"), first);

        HashPsd8::from_str("r0 into r1").evaluate(&registers);

        let value = registers.load(&Register::from_str("r1"));
        let expected = Value::<P>::from_str(
            "2132636093982099992808836832692348220698310395516022520468979890154979376079field.private",
        );
        assert_eq!(expected, value);
    }
}
