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

use crate::vm::{CircuitValue, Opcode, Operand, Program, Stack, StackValue};
use console::{
    network::prelude::*,
    program::{Literal, LiteralType, Plaintext, PlaintextType, Register, RegisterType},
};

use core::marker::PhantomData;

pub trait HashOperation<N: Network, A: circuit::Aleo<Network = N>> {
    /// The opcode of the operation.
    const OPCODE: Opcode;

    /// Returns the result of hashing the given input.
    fn evaluate(input: StackValue<N>) -> Result<StackValue<N>>;

    /// Returns the result of hashing the given circuit input.
    fn execute(input: CircuitValue<A>) -> Result<CircuitValue<A>>;

    /// Returns the output type from the given input types.
    fn output_type() -> Result<RegisterType<N>>;
}

/// BHP256 is a collision-resistant hash function that processes inputs in 256-bit chunks.
pub type HashBHP256<N, A> = HashInstruction<N, A, BHPHashOperation<N, A, 256>>;
/// BHP512 is a collision-resistant hash function that processes inputs in 512-bit chunks.
pub type HashBHP512<N, A> = HashInstruction<N, A, BHPHashOperation<N, A, 512>>;
/// BHP768 is a collision-resistant hash function that processes inputs in 768-bit chunks.
pub type HashBHP768<N, A> = HashInstruction<N, A, BHPHashOperation<N, A, 768>>;
/// BHP1024 is a collision-resistant hash function that processes inputs in 1024-bit chunks.
pub type HashBHP1024<N, A> = HashInstruction<N, A, BHPHashOperation<N, A, 1024>>;

/// The BHP hash operation template.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct BHPHashOperation<N: Network, A: circuit::Aleo<Network = N>, const NUM_BITS: u16>(PhantomData<(N, A)>);

impl<N: Network, A: circuit::Aleo<Network = N>, const NUM_BITS: u16> HashOperation<N, A>
    for BHPHashOperation<N, A, NUM_BITS>
{
    /// The opcode of the operation.
    const OPCODE: Opcode = match NUM_BITS {
        256 => Opcode::Hash("hash.bhp256"),
        512 => Opcode::Hash("hash.bhp512"),
        768 => Opcode::Hash("hash.bhp768"),
        1024 => Opcode::Hash("hash.bhp1024"),
        _ => panic!("Invalid BHP hash instruction opcode"),
    };

    /// Returns the result of hashing the given input.
    fn evaluate(input: StackValue<N>) -> Result<StackValue<N>> {
        // Convert the input into bits.
        let preimage = input.to_bits_le();
        // Hash the preimage.
        let output = match NUM_BITS {
            256 => N::hash_bhp256(&preimage)?,
            512 => N::hash_bhp512(&preimage)?,
            768 => N::hash_bhp768(&preimage)?,
            1024 => N::hash_bhp1024(&preimage)?,
            _ => bail!("Invalid BHP hash variant: BHP{}", NUM_BITS),
        };
        // Return the output as a stack value.
        Ok(StackValue::Plaintext(Plaintext::Literal(Literal::Field(output), Default::default())))
    }

    /// Returns the result of hashing the given circuit input.
    fn execute(input: CircuitValue<A>) -> Result<CircuitValue<A>> {
        // Convert the input into bits.
        let preimage = input.to_bits_le();
        // Hash the preimage.
        let output = match NUM_BITS {
            256 => A::hash_bhp256(&preimage),
            512 => A::hash_bhp512(&preimage),
            768 => A::hash_bhp768(&preimage),
            1024 => A::hash_bhp1024(&preimage),
            _ => bail!("Invalid BHP hash variant: BHP{}", NUM_BITS),
        };
        // Return the output as a stack value.
        Ok(CircuitValue::Plaintext(circuit::Plaintext::Literal(circuit::Literal::Field(output), Default::default())))
    }

    /// Returns the output type from the given input types.
    fn output_type() -> Result<RegisterType<N>> {
        Ok(RegisterType::Plaintext(PlaintextType::Literal(LiteralType::Field)))
    }
}

/// Hashes the operand into the declared type.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct HashInstruction<N: Network, A: circuit::Aleo<Network = N>, O: HashOperation<N, A>> {
    /// The operand as `input`.
    operands: Vec<Operand<N>>,
    /// The destination register.
    destination: Register<N>,
    /// PhantomData.
    _phantom: PhantomData<(A, O)>,
}

impl<N: Network, A: circuit::Aleo<Network = N>, O: HashOperation<N, A>> HashInstruction<N, A, O> {
    /// Returns the opcode.
    #[inline]
    pub const fn opcode() -> Opcode {
        O::OPCODE
    }

    /// Returns the operands in the operation.
    #[inline]
    pub fn operands(&self) -> &[Operand<N>] {
        // Sanity check that the operands is exactly one input.
        debug_assert!(self.operands.len() == 1, "Hash operation must have one operand");
        // Return the operand.
        &self.operands
    }

    /// Returns the destination register.
    #[inline]
    pub fn destinations(&self) -> Vec<Register<N>> {
        vec![self.destination.clone()]
    }
}

impl<N: Network, A: circuit::Aleo<Network = N>, O: HashOperation<N, A>> HashInstruction<N, A, O> {
    /// Evaluates the instruction.
    #[inline]
    pub fn evaluate(&self, stack: &mut Stack<N, A>) -> Result<()> {
        // Ensure the number of operands is correct.
        if self.operands.len() != 1 {
            bail!("Instruction '{}' expects 1 operands, found {} operands", Self::opcode(), self.operands.len())
        }
        // Load the operand.
        let input = stack.load(&self.operands[0])?;
        // Hash the input.
        let output = O::evaluate(input)?;
        // Store the output.
        stack.store(&self.destination, output)

        // // TODO (howardwu): Implement `Literal::to_fields()` to replace this closure.
        // // (Optional) Closure for converting a list of literals into a list of field elements.
        // //
        // // If the list is comprised of `Address`, `Field`, `Group`, and/or `Scalar`, then the closure
        // // will return the underlying field elements (instead of packing the literals from bits).
        // // Otherwise, the list is converted into bits, and then packed into field elements.
        // let to_field_elements = |input: &[Literal<_>]| {
        //     // Determine whether the input is comprised of field-friendly literals.
        //     match input.iter().all(|literal| {
        //         matches!(literal, Literal::Address(_) | Literal::Field(_) | Literal::Group(_) | Literal::Scalar(_))
        //     }) {
        //         // Case 1 - Map each literal directly to its field representation.
        //         true => input
        //             .iter()
        //             .map(|literal| match literal {
        //                 Literal::Address(address) => address.to_field(),
        //                 Literal::Field(field) => field.clone(),
        //                 Literal::Group(group) => group.to_x_coordinate(),
        //                 Literal::Scalar(scalar) => scalar.to_field(),
        //                 _ => P::halt("Unreachable literal variant detected during hashing."),
        //             })
        //             .collect::<Vec<_>>(),
        //         // Case 2 - Convert the literals to bits, and then pack them into field elements.
        //         false => input
        //             .to_bits_le()
        //             .chunks(<P::Environment as Environment>::BaseField::size_in_data_bits())
        //             .map(FromBits::from_bits_le)
        //             .collect::<Vec<_>>(),
        //     }
        // };
    }

    /// Executes the instruction.
    #[inline]
    pub fn execute(&self, stack: &mut Stack<N, A>) -> Result<()> {
        // Ensure the number of operands is correct.
        if self.operands.len() != 1 {
            bail!("Instruction '{}' expects 1 operands, found {} operands", Self::opcode(), self.operands.len())
        }
        // Load the operand.
        let input = stack.load_circuit(&self.operands[0])?;
        // Hash the input.
        let output = O::execute(input)?;
        // Store the output.
        stack.store_circuit(&self.destination, output)
    }

    /// Returns the output type from the given program and input types.
    #[inline]
    pub fn output_types(
        &self,
        _program: &Program<N, A>,
        input_types: &[RegisterType<N>],
    ) -> Result<Vec<RegisterType<N>>> {
        // Ensure the number of input types is correct.
        if input_types.len() != 1 {
            bail!("Instruction '{}' expects 1 inputs, found {} inputs", Self::opcode(), input_types.len())
        }
        // Ensure the number of operands is correct.
        if self.operands.len() != 1 {
            bail!("Instruction '{}' expects 1 operands, found {} operands", Self::opcode(), self.operands.len())
        }

        // TODO (howardwu): If the operation is Pedersen, check that it is within the number of bits.

        Ok(vec![O::output_type()?])
    }
}

impl<N: Network, A: circuit::Aleo<Network = N>, O: HashOperation<N, A>> Parser for HashInstruction<N, A, O> {
    /// Parses a string into an operation.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the opcode from the string.
        let (string, _) = tag(*Self::opcode())(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the operand from the string.
        let (string, operand) = Operand::parse(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the "into" from the string.
        let (string, _) = tag("into")(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the destination register from the string.
        let (string, destination) = Register::parse(string)?;

        Ok((string, Self { operands: vec![operand], destination, _phantom: PhantomData }))
    }
}

impl<N: Network, A: circuit::Aleo<Network = N>, O: HashOperation<N, A>> FromStr for HashInstruction<N, A, O> {
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

impl<N: Network, A: circuit::Aleo<Network = N>, O: HashOperation<N, A>> Debug for HashInstruction<N, A, O> {
    /// Prints the operation as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network, A: circuit::Aleo<Network = N>, O: HashOperation<N, A>> Display for HashInstruction<N, A, O> {
    /// Prints the operation to a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        // Ensure the number of operands is 1.
        if self.operands.len() != 1 {
            eprintln!("The number of operands must be 1, found {}", self.operands.len());
            return Err(fmt::Error);
        }
        // Print the operation.
        write!(f, "{} ", Self::opcode())?;
        write!(f, "{} ", self.operands[0])?;
        write!(f, "into {}", self.destination)
    }
}

impl<N: Network, A: circuit::Aleo<Network = N>, O: HashOperation<N, A>> FromBytes for HashInstruction<N, A, O> {
    /// Reads the operation from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the operand.
        let operands = vec![Operand::read_le(&mut reader)?];
        // Read the destination register.
        let destination = Register::read_le(&mut reader)?;
        // Return the operation.
        Ok(Self { operands, destination, _phantom: PhantomData })
    }
}

impl<N: Network, A: circuit::Aleo<Network = N>, O: HashOperation<N, A>> ToBytes for HashInstruction<N, A, O> {
    /// Writes the operation to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Ensure the number of operands is 1.
        if self.operands.len() != 1 {
            return Err(error(format!("The number of operands must be 1, found {}", self.operands.len())));
        }
        // Write the operand.
        self.operands[0].write_le(&mut writer)?;
        // Write the destination register.
        self.destination.write_le(&mut writer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use circuit::network::AleoV0;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;
    type CurrentAleo = AleoV0;

    #[test]
    fn test_parse() {
        let (string, hash) = HashBHP512::<CurrentNetwork, CurrentAleo>::parse("hash.bhp512 r0 into r1").unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");
        assert_eq!(hash.operands.len(), 1, "The number of operands is incorrect");
        assert_eq!(hash.operands[0], Operand::Register(Register::Locator(0)), "The first operand is incorrect");
        assert_eq!(hash.destination, Register::Locator(1), "The destination register is incorrect");
    }
}
