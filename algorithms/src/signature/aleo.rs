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

use crate::{
    crypto_hash::{hash_to_curve, Poseidon},
    SignatureScheme,
    SignatureSchemeOperations,
};
use snarkvm_curves::{
    templates::twisted_edwards_extended::{Affine as TEAffine, Projective as TEProjective},
    AffineCurve,
    ProjectiveCurve,
    TwistedEdwardsParameters,
};
use snarkvm_fields::{PrimeField, ToConstraintField};
use snarkvm_utilities::{
    io::{Read, Result as IoResult, Write},
    rand::Uniform,
    serialize::*,
    FromBits,
    FromBytes,
    ToBits,
    ToBytes,
};

use anyhow::{bail, Result};
use itertools::Itertools;
use rand::{CryptoRng, Rng};

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct AleoSignature<TE: TwistedEdwardsParameters> {
    pub prover_response: TE::ScalarField,
    pub verifier_challenge: TE::ScalarField,
    root_public_key: TE::BaseField,
    root_randomizer: TE::BaseField,
}

impl<TE: TwistedEdwardsParameters> AleoSignature<TE> {
    #[inline]
    pub fn root_public_key(&self) -> Result<TEAffine<TE>> {
        if let Some(element) = TEAffine::<TE>::from_x_coordinate(self.root_public_key, true) {
            if element.is_in_correct_subgroup_assuming_on_curve() {
                return Ok(element);
            }
        }

        if let Some(element) = TEAffine::<TE>::from_x_coordinate(self.root_public_key, false) {
            if element.is_in_correct_subgroup_assuming_on_curve() {
                return Ok(element);
            }
        }

        bail!("Failed to read the signature root public key")
    }

    #[inline]
    pub fn root_randomizer(&self) -> Result<TEAffine<TE>> {
        if let Some(element) = TEAffine::<TE>::from_x_coordinate(self.root_randomizer, true) {
            if element.is_in_correct_subgroup_assuming_on_curve() {
                return Ok(element);
            }
        }

        if let Some(element) = TEAffine::<TE>::from_x_coordinate(self.root_randomizer, false) {
            if element.is_in_correct_subgroup_assuming_on_curve() {
                return Ok(element);
            }
        }

        bail!("Failed to read the signature root randomizer")
    }
}

impl<TE: TwistedEdwardsParameters> FromBytes for AleoSignature<TE> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let prover_response = TE::ScalarField::read_le(&mut reader)?;
        let verifier_challenge = TE::ScalarField::read_le(&mut reader)?;
        let root_public_key = TE::BaseField::read_le(&mut reader)?;
        let root_randomizer = TE::BaseField::read_le(&mut reader)?;

        Ok(Self { prover_response, verifier_challenge, root_public_key, root_randomizer })
    }
}

impl<TE: TwistedEdwardsParameters> ToBytes for AleoSignature<TE> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.prover_response.write_le(&mut writer)?;
        self.verifier_challenge.write_le(&mut writer)?;
        self.root_public_key.write_le(&mut writer)?;
        self.root_randomizer.write_le(&mut writer)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AleoSignatureScheme<TE: TwistedEdwardsParameters>
where
    TE::BaseField: PrimeField,
{
    g_bases: Vec<TEProjective<TE>>,
    poseidon: Poseidon<TE::BaseField, 4>,
}

impl<TE: TwistedEdwardsParameters> SignatureScheme for AleoSignatureScheme<TE>
where
    TE::BaseField: PrimeField,
{
    type Parameters = Vec<TEProjective<TE>>;
    type PrivateKey = (TE::ScalarField, TE::ScalarField);
    type PublicKey = TEAffine<TE>;
    type Signature = AleoSignature<TE>;

    fn setup(message: &str) -> Self {
        assert!(TE::ScalarField::size_in_data_bits() < TE::BaseField::size_in_data_bits());

        // Compute the powers of G.
        let g_bases = {
            let (base, _, _) = hash_to_curve::<TEAffine<TE>>(message);

            let mut g = base.to_projective();
            let mut g_bases = Vec::with_capacity(TE::ScalarField::size_in_bits());
            for _ in 0..TE::ScalarField::size_in_bits() {
                g_bases.push(g);
                g.double_in_place();
            }
            g_bases
        };

        let crypto_hash = Poseidon::<TE::BaseField, 4>::setup();

        Self { g_bases, poseidon: crypto_hash }
    }

    fn parameters(&self) -> &Self::Parameters {
        &self.g_bases
    }

    ///
    /// Returns private key as (sk_sig, r_sig).
    ///
    fn generate_private_key<R: Rng + CryptoRng>(&self, rng: &mut R) -> Self::PrivateKey {
        (TE::ScalarField::rand(rng), TE::ScalarField::rand(rng))
    }

    ///
    /// Returns public key as (G^sk_sig G^r_sig G^sk_prf).
    ///
    fn generate_public_key(&self, private_key: &Self::PrivateKey) -> Self::PublicKey {
        // Extract (sk_sig, r_sig).
        let (sk_sig, r_sig) = private_key;

        // Compute G^sk_sig.
        let g_sk_sig = self.g_scalar_multiply(sk_sig);

        // Compute G^r_sig.
        let g_r_sig = self.g_scalar_multiply(r_sig);

        // We do a batch inversion to save one inversion.
        let mut to_invert = [g_sk_sig, g_r_sig];
        TEProjective::<TE>::batch_normalization(&mut to_invert);
        let [g_sk_sig_affine, g_r_sig_affine] = to_invert.map(|a| a.to_affine());

        // Compute sk_prf := RO(G^sk_sig || G^r_sig).
        let sk_prf = self.hash_to_scalar_field(&[g_sk_sig_affine.to_x_coordinate(), g_r_sig_affine.to_x_coordinate()]);

        // Compute G^sk_prf.
        let g_sk_prf = self.g_scalar_multiply(&sk_prf);

        // Compute G^sk_sig G^r_sig G^sk_prf.
        (g_sk_sig + g_r_sig + g_sk_prf).into()
    }

    ///
    /// Returns signature (c, s, G^sk_sig, G^r_sig), where:
    ///     c := Hash(G^sk_sig G^r_sig G^sk_prf, G^r, message)
    ///     s := r - c * sk_sig
    ///
    fn sign<R: Rng + CryptoRng>(
        &self,
        private_key: &Self::PrivateKey,
        message: &[bool],
        rng: &mut R,
    ) -> Result<Self::Signature> {
        // Sample a random scalar field element.
        let r = TE::ScalarField::rand(rng);

        // Compute G^r.
        let g_r = self.g_scalar_multiply(&r);

        // Extract (sk_sig, r_sig).
        let (sk_sig, r_sig) = private_key;

        // Compute G^sk_sig.
        let g_sk_sig = self.g_scalar_multiply(sk_sig);

        // Compute G^r_sig.
        let g_r_sig = self.g_scalar_multiply(r_sig);

        let mut to_invert = [g_sk_sig, g_r_sig, g_r];
        TEProjective::<TE>::batch_normalization(&mut to_invert);
        let [g_sk_sig_affine, g_r_sig_affine, g_r_affine] = to_invert.map(|a| a.to_affine());

        // Compute sk_prf := RO(G^sk_sig || G^r_sig).
        let sk_prf = self.hash_to_scalar_field(&[g_sk_sig_affine.to_x_coordinate(), g_r_sig_affine.to_x_coordinate()]);

        // Compute G^sk_prf.
        let g_sk_prf = self.g_scalar_multiply(&sk_prf);

        // Compute G^sk_sig G^r_sig G^sk_prf.
        let public_key = (g_sk_sig + g_r_sig + g_sk_prf).to_affine();

        // Compute the verifier challenge.
        let verifier_challenge = {
            // Construct the hash input (G^sk_sig G^r_sig G^sk_prf, G^r, message).
            let mut preimage = vec![];
            preimage.extend_from_slice(&public_key.to_x_coordinate().to_field_elements()?);
            preimage.extend_from_slice(&g_r_affine.to_x_coordinate().to_field_elements()?);
            preimage.push(TE::BaseField::from(message.len() as u128));
            preimage.extend_from_slice(&message.to_field_elements()?);

            // Hash to derive the verifier challenge.
            self.hash_to_scalar_field(&preimage)
        };

        // Compute the prover response.
        let prover_response = r - (verifier_challenge * sk_sig);

        Ok(AleoSignature {
            prover_response,
            verifier_challenge,
            root_public_key: g_sk_sig_affine.to_x_coordinate(),
            root_randomizer: g_r_sig_affine.to_x_coordinate(),
        })
    }

    ///
    /// Verifies (c == c') && (public_key == G^sk_sig G^r_sig G^sk_prf) where:
    ///     c' := Hash(G^sk_sig G^r_sig G^sk_prf, G^s G^sk_sig^c, message)
    ///
    fn verify(&self, public_key: &Self::PublicKey, message: &[bool], signature: &Self::Signature) -> Result<bool> {
        // Extract the signature contents.
        let AleoSignature { prover_response, verifier_challenge, root_public_key, root_randomizer } = signature;

        // Recover G^sk_sig.
        let g_sk_sig = Self::recover_from_x_coordinate(root_public_key)?;

        // Compute G^sk_sig^c.
        let g_sk_sig_c = self.scalar_multiply(g_sk_sig, verifier_challenge);

        // Compute G^r := G^s G^sk_sig^c.
        let g_r = (self.g_scalar_multiply(prover_response) + g_sk_sig_c).to_affine();

        // Compute the candidate verifier challenge.
        let candidate_verifier_challenge = {
            // Construct the hash input (G^sk_sig G^r_sig G^sk_prf, G^r, message).
            let mut preimage = vec![];
            preimage.extend_from_slice(&public_key.to_x_coordinate().to_field_elements()?);
            preimage.extend_from_slice(&g_r.to_x_coordinate().to_field_elements()?);
            preimage.push(TE::BaseField::from(message.len() as u128));
            preimage.extend_from_slice(&message.to_field_elements()?);

            // Hash to derive the verifier challenge.
            self.hash_to_scalar_field(&preimage)
        };

        // Recover G^r_sig.
        let g_r_sig = Self::recover_from_x_coordinate(root_randomizer)?;

        // Compute the candidate public key as (G^sk_sig G^r_sig G^sk_prf).
        let candidate_public_key = {
            // Compute sk_prf := RO(G^sk_sig || G^r_sig).
            let sk_prf = self.hash_to_scalar_field(&[g_sk_sig.to_x_coordinate(), g_r_sig.to_x_coordinate()]);

            // Compute G^sk_prf.
            let g_sk_prf = self.g_scalar_multiply(&sk_prf);

            // Compute G^sk_sig G^r_sig G^sk_prf.
            g_sk_sig.to_projective() + g_sk_prf + g_r_sig.to_projective()
        };

        Ok(*verifier_challenge == candidate_verifier_challenge && *public_key == candidate_public_key)
    }
}

impl<TE: TwistedEdwardsParameters> SignatureSchemeOperations for AleoSignatureScheme<TE>
where
    TE::BaseField: PrimeField,
{
    type AffineCurve = TEAffine<TE>;
    type BaseField = TE::BaseField;
    type ScalarField = TE::ScalarField;
    type Signature = AleoSignature<TE>;

    fn pk_sig(signature: &Self::Signature) -> Result<Self::AffineCurve> {
        Self::recover_from_x_coordinate(&signature.root_public_key)
    }

    fn pr_sig(signature: &Self::Signature) -> Result<Self::AffineCurve> {
        Self::recover_from_x_coordinate(&signature.root_randomizer)
    }

    fn g_scalar_multiply(&self, scalar: &Self::ScalarField) -> <Self::AffineCurve as AffineCurve>::Projective {
        self.g_bases
            .iter()
            .zip_eq(&scalar.to_bits_le())
            .filter_map(|(base, bit)| match bit {
                true => Some(base),
                false => None,
            })
            .sum::<TEProjective<TE>>()
    }

    fn hash_to_scalar_field(&self, input: &[Self::BaseField]) -> Self::ScalarField {
        // Use Poseidon as a random oracle.
        let output = self.poseidon.evaluate(input);

        // Truncate the output to CAPACITY bits (1 bit less than MODULUS_BITS) in the scalar field.
        let mut bits = output.to_bits_le();
        bits.resize(TE::ScalarField::size_in_data_bits(), false);

        // Output the scalar field.
        let biginteger = <TE::ScalarField as PrimeField>::BigInteger::from_bits_le(&bits).unwrap();
        match <TE::ScalarField as PrimeField>::from_repr(biginteger) {
            // We know this case will always work, because we truncate the output to CAPACITY bits in the scalar field.
            Some(scalar) => scalar,
            _ => panic!("Failed to hash input into scalar field"),
        }
    }
}

impl<TE: TwistedEdwardsParameters> AleoSignatureScheme<TE>
where
    TE::BaseField: PrimeField,
{
    fn scalar_multiply(&self, base: TEAffine<TE>, scalar: &TE::ScalarField) -> TEProjective<TE> {
        base * *scalar
    }

    fn recover_from_x_coordinate(x_coordinate: &TE::BaseField) -> Result<TEAffine<TE>> {
        if let Some(element) = TEAffine::<TE>::from_x_coordinate(*x_coordinate, true) {
            if element.is_in_correct_subgroup_assuming_on_curve() {
                return Ok(element);
            }
        }

        if let Some(element) = TEAffine::<TE>::from_x_coordinate(*x_coordinate, false) {
            if element.is_in_correct_subgroup_assuming_on_curve() {
                return Ok(element);
            }
        }

        bail!("Failed to recover from x coordinate")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_curves::{
        edwards_bls12::EdwardsParameters as EdwardsBls12,
        edwards_bw6::EdwardsParameters as EdwardsBW6,
    };
    use snarkvm_utilities::test_crypto_rng;

    fn sign_and_verify<S: SignatureScheme>(message: &[bool]) {
        let rng = &mut test_crypto_rng();
        let signature_scheme = S::setup("sign_and_verify");

        let private_key = signature_scheme.generate_private_key(rng);
        let public_key = signature_scheme.generate_public_key(&private_key);
        let signature = signature_scheme.sign(&private_key, message, rng).unwrap();
        assert!(signature_scheme.verify(&public_key, message, &signature).unwrap());
    }

    fn failed_verification<S: SignatureScheme>(message: &[bool], bad_message: &[bool]) {
        let rng = &mut test_crypto_rng();
        let signature_scheme = S::setup("failed_verification");

        let private_key = signature_scheme.generate_private_key(rng);
        let public_key = signature_scheme.generate_public_key(&private_key);
        let signature = signature_scheme.sign(&private_key, message, rng).unwrap();
        assert!(!signature_scheme.verify(&public_key, bad_message, &signature).unwrap());
    }

    #[test]
    fn test_aleo_signature_on_edwards_bls12_377() {
        type TestSignature = AleoSignatureScheme<EdwardsBls12>;

        let message = "Hi, I am an Aleo signature!";
        sign_and_verify::<TestSignature>(&message.as_bytes().to_bits_le());
        failed_verification::<TestSignature>(&message.as_bytes().to_bits_le(), &b"Bad message".to_bits_le());
    }

    #[test]
    fn test_aleo_signature_on_edwards_bw6() {
        type TestSignature = AleoSignatureScheme<EdwardsBW6>;

        let message = "Hi, I am an Aleo signature!";
        sign_and_verify::<TestSignature>(&message.as_bytes().to_bits_le());
        failed_verification::<TestSignature>(&message.as_bytes().to_bits_le(), &b"Bad message".to_bits_le());
    }
}
