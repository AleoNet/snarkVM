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

impl<N: Network> FromBytes for Transition<N> {
    /// Reads the output from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let program_id = FromBytes::read_le(&mut reader)?;
        let function_name = FromBytes::read_le(&mut reader)?;

        let num_inputs: u16 = FromBytes::read_le(&mut reader)?;
        let mut inputs = Vec::with_capacity(num_inputs as usize);
        for _ in 0..num_inputs {
            inputs.push(FromBytes::read_le(&mut reader)?);
        }

        let num_outputs: u16 = FromBytes::read_le(&mut reader)?;
        let mut outputs = Vec::with_capacity(num_outputs as usize);
        for _ in 0..num_outputs {
            outputs.push(FromBytes::read_le(&mut reader)?);
        }

        let proof = FromBytes::read_le(&mut reader)?;
        let tpk = FromBytes::read_le(&mut reader)?;
        let fee = FromBytes::read_le(&mut reader)?;

        Ok(Transition::new(program_id, function_name, inputs, outputs, proof, tpk, fee))
    }
}

impl<N: Network> ToBytes for Transition<N> {
    /// Writes the literal to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.program_id.write_le(&mut writer)?;
        self.function_name.write_le(&mut writer)?;

        (self.inputs.len() as u16).write_le(&mut writer)?;
        self.inputs.write_le(&mut writer)?;

        (self.outputs.len() as u16).write_le(&mut writer)?;
        self.outputs.write_le(&mut writer)?;

        self.proof.write_le(&mut writer)?;
        self.tpk.write_le(&mut writer)?;
        self.fee.write_le(&mut writer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    const ITERATIONS: u32 = 1000;

    fn check_bytes(expected: Transition<CurrentNetwork>) -> Result<()> {
        // Check the byte representation.
        let expected_bytes = expected.to_bytes_le()?;
        assert!(expected == Transition::read_le(&expected_bytes[..])?);
        assert!(Transition::<CurrentNetwork>::read_le(&expected_bytes[1..]).is_err());
        Ok(())
    }

    // #[test]
    // fn test_bytes() -> Result<()> {
    //     let rng = &mut test_rng();
    //
    //     for _ in 0..ITERATIONS {
    //         let program_id = ProgramID::<CurrentNetwork>::from_str("bar.aleo").unwrap();
    //         let (_, function_name) = Identifier::<CurrentNetwork>::parse("foo_bar1").unwrap();
    //
    //         // TODO (raychu86): Sample a proof for testing.
    //         let proof = snark::execute(assignment).unwrap();
    //
    //         // Constant
    //         let constant_inputs =
    //             (0..10).map(|_| Input::<CurrentNetwork>::Constant(Uniform::rand(rng), None)).collect::<Vec<_>>();
    //         let constant_outputs =
    //             (0..10).map(|_| Output::<CurrentNetwork>::Constant(Uniform::rand(rng), None)).collect::<Vec<_>>();
    //         let transition: Transition<CurrentNetwork> = Transition::new(
    //             program_id.clone(),
    //             function_name.clone(),
    //             constant_inputs,
    //             constant_outputs,
    //             proof.clone(),
    //             Uniform::rand(rng),
    //             Uniform::rand(rng),
    //         );
    //
    //         check_bytes(transition).unwrap();
    //
    //         // Public
    //         let public_inputs =
    //             (0..10).map(|_| Input::<CurrentNetwork>::Public(Uniform::rand(rng), None)).collect::<Vec<_>>();
    //         let public_outputs =
    //             (0..10).map(|_| Output::<CurrentNetwork>::Public(Uniform::rand(rng), None)).collect::<Vec<_>>();
    //         let transition: Transition<CurrentNetwork> = Transition::new(
    //             program_id.clone(),
    //             function_name.clone(),
    //             public_inputs,
    //             public_outputs,
    //             proof.clone(),
    //             Uniform::rand(rng),
    //             Uniform::rand(rng),
    //         );
    //
    //         check_bytes(transition).unwrap();
    //
    //         // Private
    //         let private_inputs =
    //             (0..10).map(|_| Input::<CurrentNetwork>::Private(Uniform::rand(rng), None)).collect::<Vec<_>>();
    //         let private_outputs =
    //             (0..10).map(|_| Output::<CurrentNetwork>::Private(Uniform::rand(rng), None)).collect::<Vec<_>>();
    //         let transition: Transition<CurrentNetwork> = Transition::new(
    //             program_id.clone(),
    //             function_name.clone(),
    //             private_inputs,
    //             private_outputs,
    //             proof.clone(),
    //             Uniform::rand(rng),
    //             Uniform::rand(rng),
    //         );
    //
    //         check_bytes(transition).unwrap();
    //
    //         // Record
    //         let record_inputs =
    //             (0..10).map(|_| Input::<CurrentNetwork>::Record(Uniform::rand(rng))).collect::<Vec<_>>();
    //         let record_outputs = (0..10)
    //             .map(|_| {
    //                 Output::<CurrentNetwork>::Record(Uniform::rand(rng), Uniform::rand(rng), Uniform::rand(rng), None)
    //             })
    //             .collect::<Vec<_>>();
    //         let transition: Transition<CurrentNetwork> = Transition::new(
    //             program_id,
    //             function_name,
    //             record_inputs,
    //             record_outputs,
    //             proof,
    //             Uniform::rand(rng),
    //             Uniform::rand(rng),
    //         );
    //
    //         check_bytes(transition).unwrap();
    //     }
    //     Ok(())
    // }
}
