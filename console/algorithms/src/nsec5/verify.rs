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

impl<
    G: AffineCurve<Coordinates = (BaseField<G>, BaseField<G>)>,
    P: MontgomeryParameters<BaseField = BaseField<G>> + TwistedEdwardsParameters<BaseField = BaseField<G>>,
> NSEC5<G, P>
where
    <G as AffineCurve>::BaseField: PrimeField,
{
    /// Returns `true` if the proof is valid, and `false` otherwise.
    pub fn verify(
        &self,
        generator_g: G,
        poseidon: &Poseidon4<BaseField<G>>,
        pk_vrf: G,
        input: &[BaseField<G>],
    ) -> bool {
        // Retrieve the proof components.
        let (gamma, challenge, response) = self.proof;

        // Compute the generator `H` as `MapToCurve(HashMany(input)[0]) + MapToCurve(HashMany(input)[1])`.
        let generator_h = match poseidon.hash_many(input, 2).iter().map(Elligator2::<G, P>::encode).collect_tuple() {
            Some((Ok((h0, _)), Ok((h1, _)))) => h0.to_projective() + h1.to_projective(),
            _ => {
                eprintln!("VRF failed to encode the hashes from the given input");
                return false;
            }
        };

        // Compute `u` as `(challenge * pk_vrf) + (response * G)`, equivalent to `randomizer * G`.
        let u: G = ((pk_vrf.to_projective() * challenge) + (generator_g.to_projective() * response)).to_affine();

        // Compute `v` as `(challenge * gamma) + (response * H)`, equivalent to `randomizer * H`.
        let v: G = ((gamma.to_projective() * challenge) + (generator_h * response)).to_affine();

        // Compute `candidate_challenge` as `HashToScalar(pk_vrf, gamma, randomizer * G, randomizer * H)`.
        let candidate_challenge: ScalarField<G> =
            match poseidon.hash_to_scalar(&[pk_vrf, gamma, u, v].map(|c| c.to_x_coordinate())) {
                Ok(candidate_challenge) => candidate_challenge,
                Err(err) => {
                    eprintln!("VRF failed to compute the challenge: {}", err);
                    return false;
                }
            };

        // Compute `candidate_output` as `HashToScalar(COFACTOR * gamma)`.
        let candidate_output: ScalarField<G> =
            match poseidon.hash_to_scalar(&[gamma.mul_by_cofactor().to_x_coordinate()]) {
                Ok(candidate_output) => candidate_output,
                Err(err) => {
                    eprintln!("VRF failed to compute the output: {}", err);
                    return false;
                }
            };

        // Return whether the proof is valid.
        println!("{}: {challenge} {candidate_challenge}", challenge == candidate_challenge);
        println!("{}", self.output == candidate_output);
        challenge == candidate_challenge && self.output == candidate_output
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_curves::edwards_bls12::{EdwardsAffine, EdwardsParameters, Fq};
    use snarkvm_utilities::{test_rng, UniformRand};

    pub(crate) const ITERATIONS: usize = 10000;

    #[test]
    fn test_prove_and_verify() -> Result<()> {
        let rng = &mut test_rng();
        let poseidon4 = Poseidon4::<Fq>::setup();

        for _ in 0..ITERATIONS {
            let generator_g: EdwardsAffine = UniformRand::rand(rng);
            let sk_vrf = UniformRand::rand(rng);
            let input: Fq = UniformRand::rand(rng);
            let randomizer = UniformRand::rand(rng);

            let pk_vrf = (generator_g.to_projective() * sk_vrf).to_affine();

            let proof = NSEC5::<EdwardsAffine, EdwardsParameters>::prove(
                generator_g,
                &poseidon4,
                &sk_vrf,
                &[input],
                randomizer,
            )?;
            assert!(proof.verify(generator_g, &poseidon4, pk_vrf, &[input]));
        }
        Ok(())
    }
}
