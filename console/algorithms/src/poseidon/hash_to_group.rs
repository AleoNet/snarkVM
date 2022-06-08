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

impl<F: PrimeField, const RATE: usize> HashToGroup for Poseidon<F, RATE> {
    type Field = F;
    type Input = F;

    /// Returns an affine group element from hashing the input.
    #[inline]
    fn hash_to_group<
        G: AffineCurve<BaseField = Self::Field, Coordinates = (Self::Field, Self::Field)>,
        P: MontgomeryParameters<BaseField = Self::Field> + TwistedEdwardsParameters<BaseField = Self::Field>,
    >(
        &self,
        input: &[Self::Input],
    ) -> Result<G> {
        // Ensure that the input is not empty.
        ensure!(!input.is_empty(), "Input to hash to group cannot be empty");
        // Compute the group element as `MapToGroup(HashMany(input)[0]) + MapToGroup(HashMany(input)[1])`.
        match self.hash_many(input, 2).iter().map(Elligator2::<G, P>::encode).collect_tuple() {
            Some((Ok((h0, _)), Ok((h1, _)))) => Ok((h0.to_projective() + h1.to_projective()).to_affine()),
            _ => bail!("Poseidon failed to compute hash to group on the given input"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_curves::edwards_bls12::{EdwardsAffine, EdwardsParameters, Fq};
    use snarkvm_fields::Zero;
    use snarkvm_utilities::{test_rng, Uniform};

    const ITERATIONS: u64 = 1000;

    macro_rules! check_hash_to_group {
        ($poseidon:ident) => {{
            // Initialize Poseidon.
            let poseidon = $poseidon::<Fq>::setup("HashToGroupTest")?;

            // Ensure an empty input fails.
            assert!(poseidon.hash_to_group::<EdwardsAffine, EdwardsParameters>(&[]).is_err());

            for _ in 0..ITERATIONS {
                for num_inputs in 1..8 {
                    // Sample random field elements.
                    let inputs = (0..num_inputs).map(|_| UniformRand::rand(&mut test_rng())).collect::<Vec<_>>();

                    // Compute the hash to group.
                    let candidate = poseidon.hash_to_group::<EdwardsAffine, EdwardsParameters>(&inputs)?;
                    assert!(candidate.is_on_curve());
                    assert!(candidate.is_in_correct_subgroup_assuming_on_curve());
                    assert_ne!(EdwardsAffine::zero(), candidate);
                    assert_ne!(EdwardsAffine::prime_subgroup_generator(), candidate);

                    let candidate_cofactor_inv = candidate.mul_by_cofactor_inv();
                    assert_eq!(candidate, candidate_cofactor_inv.mul_by_cofactor());
                }
            }
            Ok(())
        }};
    }

    #[test]
    fn test_poseidon2_hash_to_group() -> Result<()> {
        check_hash_to_group!(Poseidon2)
    }

    #[test]
    fn test_poseidon4_hash_to_group() -> Result<()> {
        check_hash_to_group!(Poseidon4)
    }

    #[test]
    fn test_poseidon8_hash_to_group() -> Result<()> {
        check_hash_to_group!(Poseidon8)
    }
}
