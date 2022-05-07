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

/// Performs a Poseidon hash with an input rate of 4.
pub type HashPsd4<P> = Hash<P, Psd4>;

pub struct Psd4;
impl HashOpcode for Psd4 {
    const OPCODE: &'static str = "hash.psd4";
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        function::{Instruction, Operation, Registers},
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
        let (_, instruction) = Instruction::<P>::parse("hash.psd4 r0 into r1;").unwrap();
        assert!(matches!(instruction, Instruction::HashPsd4(_)));
    }

    test_modes!(
        address,
        HashPsd4,
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah",
        "3643441450998764817137352407460510301366206136830721502689693475105463182192field"
    );
    test_modes!(
        bool,
        HashPsd4,
        "true",
        "1088580045362314438112823188316979551898376415861015087020772893540491855029field"
    );
    test_modes!(
        field,
        HashPsd4,
        "1field",
        "1088580045362314438112823188316979551898376415861015087020772893540491855029field"
    );
    test_modes!(
        group,
        HashPsd4,
        "2group",
        "1275708575393142722110884605606718473266154956117494535950447535984426072340field"
    );
    test_modes!(
        i8,
        HashPsd4,
        "1i8",
        "1088580045362314438112823188316979551898376415861015087020772893540491855029field"
    );
    test_modes!(
        i16,
        HashPsd4,
        "1i16",
        "1088580045362314438112823188316979551898376415861015087020772893540491855029field"
    );
    test_modes!(
        i32,
        HashPsd4,
        "1i32",
        "1088580045362314438112823188316979551898376415861015087020772893540491855029field"
    );
    test_modes!(
        i64,
        HashPsd4,
        "1i64",
        "1088580045362314438112823188316979551898376415861015087020772893540491855029field"
    );
    test_modes!(
        i128,
        HashPsd4,
        "1i128",
        "1088580045362314438112823188316979551898376415861015087020772893540491855029field"
    );
    test_modes!(
        u8,
        HashPsd4,
        "1u8",
        "1088580045362314438112823188316979551898376415861015087020772893540491855029field"
    );
    test_modes!(
        u16,
        HashPsd4,
        "1u16",
        "1088580045362314438112823188316979551898376415861015087020772893540491855029field"
    );
    test_modes!(
        u32,
        HashPsd4,
        "1u32",
        "1088580045362314438112823188316979551898376415861015087020772893540491855029field"
    );
    test_modes!(
        u64,
        HashPsd4,
        "1u64",
        "1088580045362314438112823188316979551898376415861015087020772893540491855029field"
    );
    test_modes!(
        u128,
        HashPsd4,
        "1u128",
        "1088580045362314438112823188316979551898376415861015087020772893540491855029field"
    );
    test_modes!(
        scalar,
        HashPsd4,
        "1scalar",
        "1088580045362314438112823188316979551898376415861015087020772893540491855029field"
    );
    test_modes!(
        string,
        HashPsd4,
        "\"aaaaaaaa\"",
        "4167190024968967735724650291761534994019909311594675614398942316879984619698field"
    );

    #[test]
    fn test_composite() {
        let first = Value::<P>::Composite(Identifier::from_str("message"), vec![
            Literal::from_str("1field.public"),
            Literal::from_str("2field.private"),
        ]);

        let registers = Registers::<P>::default();
        registers.define(&Register::from_str("r0"));
        registers.define(&Register::from_str("r1"));
        registers.assign(&Register::from_str("r0"), first);

        HashPsd4::from_str("r0 into r1").evaluate(&registers);

        let value = registers.load(&Register::from_str("r1"));
        let expected = Value::<P>::from_str(
            "7410955135478997215580161365440101606333606243972831046907054658477903053702field.private",
        );
        assert_eq!(expected, value);
    }
}
