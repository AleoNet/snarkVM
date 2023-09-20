// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use crate::{CallOperator, Opcode};
use console::{network::prelude::*, program::Register};

/// Calls the operands into the declared type.
/// i.e. `call.finalize transfer r0 r1;`
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct CallFinalize<N: Network> {
    /// The reference.
    operator: CallOperator<N>,
    /// The callee input registers.
    inputs: Vec<Register<N>>,
}

impl<N: Network> CallFinalize<N> {
    /// Returns the opcode.
    #[inline]
    pub const fn opcode() -> Opcode {
        Opcode::Call("call.finalize")
    }

    /// Return the operator.
    #[inline]
    pub const fn operator(&self) -> &CallOperator<N> {
        &self.operator
    }

    /// Returns the finalize input registers.
    #[inline]
    pub fn inputs(&self) -> &[Register<N>] {
        &self.inputs
    }
}

impl<N: Network> Parser for CallFinalize<N> {
    /// Parses a string into an operation.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        /// Parses a register from the string.
        fn parse_register<N: Network>(string: &str) -> ParserResult<Register<N>> {
            // Parse the whitespace from the string.
            let (string, _) = Sanitizer::parse_whitespaces(string)?;
            // Parse the destination from the string.
            Register::parse(string)
        }
        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the opcode from the string.
        let (string, _) = tag(*Self::opcode())(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the name of the call from the string.
        let (string, operator) = CallOperator::parse(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the input registers from the string.
        let (string, inputs) = map_res(many0(complete(parse_register)), |inputs: Vec<Register<N>>| {
            // Ensure the number of operands is within the bounds.
            match inputs.len() <= N::MAX_OPERANDS {
                true => Ok(inputs),
                false => Err(error("Failed to parse 'call.finalize' opcode: too many operands")),
            }
        })(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the ";" from the string.
        let (string, _) = tag(";")(string)?;

        Ok((string, Self { operator, inputs }))
    }
}

impl<N: Network> FromStr for CallFinalize<N> {
    type Err = Error;

    /// Parses a string into an operation.
    #[inline]
    fn from_str(string: &str) -> Result<Self> {
        match Self::parse(string) {
            Ok((remainder, object)) => {
                // Ensure the remainder is empty.
                ensure!(remainder.is_empty(), "Failed to parse string. Found invalid character in: \"{remainder}\"");
                // Return the object.
                Ok(object)
            }
            Err(error) => bail!("Failed to parse string. {error}"),
        }
    }
}

impl<N: Network> Debug for CallFinalize<N> {
    /// Prints the operation as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for CallFinalize<N> {
    /// Prints the operation to a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        // Ensure the number of operands is within the bounds.
        if self.inputs.len() > N::MAX_OPERANDS {
            return Err(fmt::Error);
        }
        // Print the operation.
        write!(f, "{} {}", Self::opcode(), self.operator)?;
        self.inputs.iter().try_for_each(|operand| write!(f, " {operand}"))?;
        write!(f, ";")
    }
}

impl<N: Network> FromBytes for CallFinalize<N> {
    /// Reads the operation from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the operator of the call.
        let operator = CallOperator::read_le(&mut reader)?;

        // Read the number of inputs.
        let num_inputs = u8::read_le(&mut reader)? as usize;
        // Ensure the number of inputs is within the bounds.
        if num_inputs > N::MAX_OPERANDS {
            return Err(error(format!("The number of inputs must be <= {}", N::MAX_OPERANDS)));
        }

        // Initialize the vector for the inputs.
        let mut inputs = Vec::with_capacity(num_inputs);
        // Read the operands.
        for _ in 0..num_inputs {
            inputs.push(Register::read_le(&mut reader)?);
        }

        // Return the operation.
        Ok(Self { operator, inputs })
    }
}

impl<N: Network> ToBytes for CallFinalize<N> {
    /// Writes the operation to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Ensure the number of inputs is within the bounds.
        if self.inputs.len() > N::MAX_OPERANDS {
            return Err(error(format!("The number of inputs must be <= {}", N::MAX_OPERANDS)));
        }

        // Write the name of the call.
        self.operator.write_le(&mut writer)?;
        // Write the number of inputs.
        u8::try_from(self.inputs.len()).map_err(|e| error(e.to_string()))?.write_le(&mut writer)?;
        // Write the inputs.
        self.inputs.iter().try_for_each(|operand| operand.write_le(&mut writer))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    const FINALIZE_TEST_CASES: &[&str] = &[
        "call.finalize foo;",
        "call.finalize foo r0;",
        "call.finalize foo r0 r1;",
        "call.finalize foo r0 r1 r2;",
        "call.finalize credits.aleo/mint;",
        "call.finalize credits.aleo/mint r0;",
        "call.finalize credits.aleo/mint r0 r1;",
        "call.finalize credits.aleo/mint r0 r1 r2;",
    ];

    fn check_parser(
        string: &str,
        expected_operator: CallOperator<CurrentNetwork>,
        expected_inputs: Vec<Register<CurrentNetwork>>,
    ) {
        // Check that the parser works.
        let (string, call) = CallFinalize::parse(string).unwrap();

        // Check that the entire string was consumed.
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");

        // Check that the operator is correct.
        assert_eq!(call.operator, expected_operator, "The call operator is incorrect");

        // Check that the inputs are correct.
        assert_eq!(call.inputs.len(), expected_inputs.len(), "The number of operands is incorrect");
        for (i, (given, expected)) in call.inputs.iter().zip(expected_inputs.iter()).enumerate() {
            assert_eq!(given, expected, "The {i}-th operand is incorrect");
        }
    }

    #[test]
    fn test_parse() {
        check_parser("call.finalize transfer r0 r1;", CallOperator::from_str("transfer").unwrap(), vec![
            Register::Locator(0u64),
            Register::Locator(1u64),
        ]);

        check_parser(
            "call.finalize credits.aleo/mint_public r0 r1;",
            CallOperator::from_str("credits.aleo/mint_public").unwrap(),
            vec![Register::Locator(0u64), Register::Locator(1u64)],
        );

        check_parser("call.finalize get_magic_number r0;", CallOperator::from_str("get_magic_number").unwrap(), vec![
            Register::Locator(0u64),
        ]);

        check_parser("call.finalize noop;", CallOperator::from_str("noop").unwrap(), vec![]);
    }

    #[test]
    fn test_display() {
        for expected in FINALIZE_TEST_CASES {
            assert_eq!(CallFinalize::<CurrentNetwork>::from_str(expected).unwrap().to_string(), *expected);
        }
    }

    #[test]
    fn test_bytes() {
        for case in FINALIZE_TEST_CASES {
            let expected = CallFinalize::<CurrentNetwork>::from_str(case).unwrap();

            // Check the byte representation.
            let expected_bytes = expected.to_bytes_le().unwrap();
            assert_eq!(expected, CallFinalize::read_le(&expected_bytes[..]).unwrap());
            assert!(CallFinalize::<CurrentNetwork>::read_le(&expected_bytes[1..]).is_err());
        }
    }
}
