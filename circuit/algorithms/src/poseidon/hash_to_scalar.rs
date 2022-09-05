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

impl<E: Environment, const RATE: usize> HashToScalar for Poseidon<E, RATE> {
    type Input = Field<E>;
    type Scalar = Scalar<E>;

    /// Returns a scalar from hashing the input.
    /// This method uses truncation (up to data bits) to project onto the scalar field.
    #[inline]
    fn hash_to_scalar(&self, input: &[Self::Input]) -> Self::Scalar {
        // Hash the input to the base field.
        let output = self.hash(input);

        // Truncate the output to the size in data bits (1 bit less than the MODULUS) of the scalar.
        // Slicing here is safe as the base field is larger than the scalar field.
        Scalar::from_bits_le(&output.to_bits_le()[..E::ScalarField::size_in_data_bits()])
    }
}

#[cfg(all(test, console))]
mod tests {
    use super::*;
    use snarkvm_circuit_types::environment::Circuit;

    use anyhow::Result;

    const DOMAIN: &str = "PoseidonCircuit0";
    const ITERATIONS: usize = 10;
    const RATE: usize = 4;

    fn check_hash_to_scalar(
        mode: Mode,
        num_inputs: usize,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
    ) -> Result<()> {
        use console::HashToScalar as H;

        let native = console::Poseidon::<<Circuit as Environment>::Network, RATE>::setup(DOMAIN)?;
        let poseidon = Poseidon::<Circuit, RATE>::constant(native.clone());

        for i in 0..ITERATIONS {
            // Prepare the preimage.
            let native_input = (0..num_inputs).map(|_| Uniform::rand(&mut test_rng())).collect::<Vec<_>>();
            let input = native_input.iter().map(|v| Field::<Circuit>::new(mode, *v)).collect::<Vec<_>>();

            // Compute the native hash to scalar.
            let expected = native.hash_to_scalar(&native_input)?;

            // Compute the circuit hash.
            Circuit::scope(format!("Poseidon {mode} {i}"), || {
                let candidate = poseidon.hash_to_scalar(&input);
                assert_eq!(expected, candidate.eject_value());
                let case = format!("(mode = {mode}, num_inputs = {num_inputs})");
                assert_scope!(case, num_constants, num_public, num_private, num_constraints);
            });
            Circuit::reset();
        }
        Ok(())
    }

    #[test]
    fn test_hash_to_scalar_constant() -> Result<()> {
        for num_inputs in 0..=RATE {
            check_hash_to_scalar(Mode::Constant, num_inputs, 254, 0, 0, 0)?;
        }
        Ok(())
    }

    #[test]
    fn test_hash_to_scalar_public() -> Result<()> {
        check_hash_to_scalar(Mode::Public, 0, 254, 0, 0, 0)?;
        check_hash_to_scalar(Mode::Public, 1, 1, 0, 588, 589)?;
        check_hash_to_scalar(Mode::Public, 2, 1, 0, 593, 594)?;
        check_hash_to_scalar(Mode::Public, 3, 1, 0, 598, 599)?;
        check_hash_to_scalar(Mode::Public, 4, 1, 0, 603, 604)?;
        check_hash_to_scalar(Mode::Public, 5, 1, 0, 958, 959)?;
        check_hash_to_scalar(Mode::Public, 6, 1, 0, 958, 959)?;
        check_hash_to_scalar(Mode::Public, 7, 1, 0, 958, 959)?;
        check_hash_to_scalar(Mode::Public, 8, 1, 0, 958, 959)?;
        check_hash_to_scalar(Mode::Public, 9, 1, 0, 1313, 1314)?;
        check_hash_to_scalar(Mode::Public, 10, 1, 0, 1313, 1314)
    }

    #[test]
    fn test_hash_to_scalar_private() -> Result<()> {
        check_hash_to_scalar(Mode::Private, 0, 254, 0, 0, 0)?;
        check_hash_to_scalar(Mode::Private, 1, 1, 0, 588, 589)?;
        check_hash_to_scalar(Mode::Private, 2, 1, 0, 593, 594)?;
        check_hash_to_scalar(Mode::Private, 3, 1, 0, 598, 599)?;
        check_hash_to_scalar(Mode::Private, 4, 1, 0, 603, 604)?;
        check_hash_to_scalar(Mode::Private, 5, 1, 0, 958, 959)?;
        check_hash_to_scalar(Mode::Private, 6, 1, 0, 958, 959)?;
        check_hash_to_scalar(Mode::Private, 7, 1, 0, 958, 959)?;
        check_hash_to_scalar(Mode::Private, 8, 1, 0, 958, 959)?;
        check_hash_to_scalar(Mode::Private, 9, 1, 0, 1313, 1314)?;
        check_hash_to_scalar(Mode::Private, 10, 1, 0, 1313, 1314)
    }
}
