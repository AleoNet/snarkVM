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

/// Performs a Poseidon PRF with an input rate of 8.
pub type PRFPsd8<P> = PRF<P, Psd8>;

pub struct Psd8;
impl PRFOpcode for Psd8 {
    const OPCODE: &'static str = "prf.psd8";
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        function::{Instruction, Operation, Register, Registers},
        Identifier,
        Process,
        Value,
    };
    use snarkvm_circuit::Parser;

    type P = Process;

    #[ignore]
    #[test]
    fn test_parse() {
        let (_, instruction) = Instruction::<P>::parse("prf.psd8 r0 r1 into r2;").unwrap();
        assert!(matches!(instruction, Instruction::PRFPsd8(_)));
    }

    // test_modes!(
    //     address,
    //     PRFPsd8,
    //     "1field",
    //     "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah",
    //     "4078625192409902085498893670047902369391416999400289383327270496814322602813field"
    // );
    // test_modes!(
    //     bool,
    //     PRFPsd8,
    //     "1field",
    //     "true",
    //     "6791106090222606057175427403347198633485235453302566023285413894036433522392field"
    // );
    // test_modes!(
    //     field,
    //     PRFPsd8,
    //     "1field",
    //     "1field",
    //     "6791106090222606057175427403347198633485235453302566023285413894036433522392field"
    // );
    // test_modes!(
    //     group,
    //     PRFPsd8,
    //     "1field",
    //     "2group",
    //     "4299285651424993918421974417521338168509527605350518900862708491597196294070field"
    // );
    // test_modes!(
    //     i8,
    //     PRFPsd8,
    //     "1field",
    //     "1i8",
    //     "6791106090222606057175427403347198633485235453302566023285413894036433522392field"
    // );
    // test_modes!(
    //     i16,
    //     PRFPsd8,
    //     "1field",
    //     "1i16",
    //     "6791106090222606057175427403347198633485235453302566023285413894036433522392field"
    // );
    // test_modes!(
    //     i32,
    //     PRFPsd8,
    //     "1field",
    //     "1i32",
    //     "6791106090222606057175427403347198633485235453302566023285413894036433522392field"
    // );
    // test_modes!(
    //     i64,
    //     PRFPsd8,
    //     "1field",
    //     "1i64",
    //     "6791106090222606057175427403347198633485235453302566023285413894036433522392field"
    // );
    // test_modes!(
    //     i128,
    //     PRFPsd8,
    //     "1field",
    //     "1i128",
    //     "6791106090222606057175427403347198633485235453302566023285413894036433522392field"
    // );
    // test_modes!(
    //     u8,
    //     PRFPsd8,
    //     "1field",
    //     "1u8",
    //     "6791106090222606057175427403347198633485235453302566023285413894036433522392field"
    // );
    // test_modes!(
    //     u16,
    //     PRFPsd8,
    //     "1field",
    //     "1u16",
    //     "6791106090222606057175427403347198633485235453302566023285413894036433522392field"
    // );
    // test_modes!(
    //     u32,
    //     PRFPsd8,
    //     "1field",
    //     "1u32",
    //     "6791106090222606057175427403347198633485235453302566023285413894036433522392field"
    // );
    // test_modes!(
    //     u64,
    //     PRFPsd8,
    //     "1field",
    //     "1u64",
    //     "6791106090222606057175427403347198633485235453302566023285413894036433522392field"
    // );
    // test_modes!(
    //     u128,
    //     PRFPsd8,
    //     "1field",
    //     "1u128",
    //     "6791106090222606057175427403347198633485235453302566023285413894036433522392field"
    // );
    // test_modes!(
    //     scalar,
    //     PRFPsd8,
    //     "1field",
    //     "1scalar",
    //     "6791106090222606057175427403347198633485235453302566023285413894036433522392field"
    // );
    // test_modes!(
    //     string,
    //     PRFPsd8,
    //     "1field",
    //     "\"aaaaaaaa\"",
    //     "5841122759472901961101257561485425983545385171455515764305377895994233987601field"
    // );
    //
    // test_instruction_halts!(
    //     wrong_seed,
    //     PRFPsd8,
    //     "Invalid seed type for PRF, expected a field element",
    //     "1scalar",
    //     "1u8"
    // );

    #[ignore]
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

        PRFPsd8::from_str("r0 r1 into r2").evaluate(&registers);

        let value = registers.load(&Register::from_str("r2"));
        let expected = Value::<P>::from_str(
            "7361945891118470894912163657103893417361583984636664095312632138077866929638field.private",
        );
        assert_eq!(expected, value);
    }
}
