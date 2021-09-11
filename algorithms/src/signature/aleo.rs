// Copyright (C) 2019-2021 Aleo Systems Inc.
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
    crypto_hash::{PoseidonCryptoHash, PoseidonDefaultParametersField},
    hash_to_curve::hash_to_curve,
    CryptoHash,
    SignatureError,
    SignatureScheme,
};
use snarkvm_curves::{
    templates::twisted_edwards_extended::{Affine as TEAffine, Projective as TEProjective},
    AffineCurve,
    Group,
    ProjectiveCurve,
    TwistedEdwardsParameters,
};
use snarkvm_fields::{ConstraintFieldError, Field, FieldParameters, PrimeField, ToConstraintField};
use snarkvm_utilities::{
    bytes::{from_bytes_le_to_bits_le, FromBytes, ToBytes},
    io::{Read, Result as IoResult, Write},
    ops::Mul,
    rand::UniformRand,
    serialize::*,
    FromBits,
    ToBits,
};

use anyhow::{anyhow, Result};
use itertools::Itertools;
use rand::{CryptoRng, Rng};

#[derive(Derivative)]
#[derivative(
    Copy(bound = "TE: TwistedEdwardsParameters"),
    Clone(bound = "TE: TwistedEdwardsParameters"),
    PartialEq(bound = "TE: TwistedEdwardsParameters"),
    Eq(bound = "TE: TwistedEdwardsParameters"),
    Debug(bound = "TE: TwistedEdwardsParameters"),
    Default(bound = "TE: TwistedEdwardsParameters")
)]
pub struct AleoSignature<TE: TwistedEdwardsParameters> {
    pub prover_response: TE::ScalarField,
    pub verifier_challenge: TE::ScalarField,
    pub sigma_public_key: TE::BaseField,
    pub sigma_response: TE::ScalarField,
}

impl<TE: TwistedEdwardsParameters> ToBytes for AleoSignature<TE> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.prover_response.write_le(&mut writer)?;
        self.verifier_challenge.write_le(&mut writer)?;
        self.sigma_public_key.write_le(&mut writer)?;
        self.sigma_response.write_le(&mut writer)
    }
}

impl<TE: TwistedEdwardsParameters> FromBytes for AleoSignature<TE> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let prover_response = TE::ScalarField::read_le(&mut reader)?;
        let verifier_challenge = TE::ScalarField::read_le(&mut reader)?;
        let sigma_public_key = TE::BaseField::read_le(&mut reader)?;
        let sigma_response = TE::ScalarField::read_le(&mut reader)?;

        Ok(Self {
            prover_response,
            verifier_challenge,
            sigma_public_key,
            sigma_response,
        })
    }
}

#[derive(Derivative)]
#[derivative(
    Clone(bound = "TE: TwistedEdwardsParameters"),
    Debug(bound = "TE: TwistedEdwardsParameters"),
    PartialEq(bound = "TE: TwistedEdwardsParameters"),
    Eq(bound = "TE: TwistedEdwardsParameters")
)]
pub struct AleoSignatureScheme<TE: TwistedEdwardsParameters> {
    pub g_bases: Vec<TEProjective<TE>>,
    pub h_bases: Vec<TEProjective<TE>>,
}

impl<TE: TwistedEdwardsParameters> SignatureScheme for AleoSignatureScheme<TE>
where
    TE::BaseField: PoseidonDefaultParametersField,
{
    type Parameters = (Vec<TEProjective<TE>>, Vec<TEProjective<TE>>);
    type PrivateKey = TE::ScalarField;
    type PublicKey = TE::BaseField;
    type Signature = AleoSignature<TE>;

    fn setup(message: &str) -> Self {
        assert!(
            <TE::ScalarField as PrimeField>::Parameters::CAPACITY < <TE::BaseField as PrimeField>::Parameters::CAPACITY
        );

        // Round to the closest multiple of 64 to factor bit and byte encoding differences.
        let private_key_size_in_bits = Self::PrivateKey::size_in_bits();
        assert!(private_key_size_in_bits < usize::MAX - 63);
        let num_powers = (private_key_size_in_bits + 63) & !63usize;

        // Compute the powers of G.
        let g_bases = {
            let (base, _, _) = hash_to_curve::<TEAffine<TE>>(&format!("{} for G", message));

            let mut g = base.into_projective();
            let mut g_bases = Vec::with_capacity(num_powers);
            for _ in 0..num_powers {
                g_bases.push(g);
                g.double_in_place();
            }
            g_bases
        };

        // Compute the powers of H.
        let h_bases = {
            let (base, _, _) = hash_to_curve::<TEAffine<TE>>(&format!("{} for H", message));

            let mut h = base.into_projective();
            let mut h_bases = Vec::with_capacity(num_powers);
            for _ in 0..num_powers {
                h_bases.push(h);
                h.double_in_place();
            }
            h_bases
        };

        Self { g_bases, h_bases }
    }

    fn parameters(&self) -> Self::Parameters {
        (self.g_bases.clone(), self.h_bases.clone())
    }

    fn generate_private_key<R: Rng + CryptoRng>(&self, rng: &mut R) -> Result<Self::PrivateKey, SignatureError> {
        Ok(TE::ScalarField::rand(rng))
    }

    fn generate_public_key(&self, private_key: &Self::PrivateKey) -> Result<Self::PublicKey, SignatureError> {
        // Compute G^sk_sig.
        let g_sk_sig = self.g_scalar_multiply(&private_key)?;

        // Compute H^sk_sig.
        let h_sk_sig = self.h_scalar_multiply(&private_key)?;

        // Compute sk_prf := RO(G^sk_sig).
        let sk_prf = self.hash_to_scalar_field(&[g_sk_sig.x])?;

        // Compute H^sk_prf.
        let h_sk_prf = self.h_scalar_multiply(&sk_prf)?;

        // Compute H^sk_sig H^sk_prf.
        let public_key = h_sk_sig + h_sk_prf;

        Ok(public_key.x)
    }

    ///
    /// Returns signature (p, d, G^sk_sig, z), where:
    ///     p := r1 - d * sk_sig
    ///     z := r2 + d * sk_sig
    ///     d := Hash(G^sk_sig, G^r1, H^sk_sig, H^r1, message)
    ///
    fn sign<R: Rng + CryptoRng>(
        &self,
        private_key: &Self::PrivateKey,
        message: &[u8],
        rng: &mut R,
    ) -> Result<Self::Signature> {
        // Sample two distinct random scalar field elements.
        let r1 = TE::ScalarField::rand(rng);
        let mut r2 = TE::ScalarField::rand(rng);
        while r1 == r2 {
            // Ensure r1 and r2 are distinct
            r2 = TE::ScalarField::rand(rng);
        }

        // Compute G^r1.
        let g_r1 = self.g_scalar_multiply(&r1)?;

        // Compute H^r1.
        let h_r1 = self.h_scalar_multiply(&r1)?;

        // Compute G^sk_sig.
        let g_sk_sig = self.g_scalar_multiply(&private_key)?;

        // Compute H^sk_sig.
        let h_sk_sig = self.h_scalar_multiply(&private_key)?;

        // Compute the verifier challenge.
        let verifier_challenge = {
            // Construct the hash input (G^sk_sig, G^r1, H^sk_sig, H^r1, message).
            let mut preimage = vec![];
            preimage.extend_from_slice(&g_sk_sig.x.to_field_elements()?);
            preimage.extend_from_slice(&g_r1.x.to_field_elements()?);
            preimage.extend_from_slice(&h_sk_sig.x.to_field_elements()?);
            preimage.extend_from_slice(&h_r1.x.to_field_elements()?);
            preimage.push(TE::BaseField::from(message.len() as u128));
            preimage.extend_from_slice(&message.to_field_elements()?);

            // Hash to derive the verifier challenge.
            self.hash_to_scalar_field(&preimage)?
        };

        // Compute the prover response.
        let prover_response = r1 - (verifier_challenge * private_key);

        // Compute the sigma response.
        let sigma_response = r2 + (verifier_challenge * private_key);

        Ok(AleoSignature {
            prover_response,
            verifier_challenge,
            sigma_public_key: g_sk_sig.x,
            sigma_response,
        })
    }

    ///
    /// Verifies (d == d') && (G^z == G^r2 G^sk_sig^d) && (H^z == H^r2 H^sk_sig^d), where:
    ///     z := r2 + d * sk_sig
    ///     d := Hash(G^sk_sig, G^r1, H^sk_sig, H^r1, message)
    ///
    fn verify(&self, public_key: &Self::PublicKey, message: &[u8], signature: &Self::Signature) -> Result<bool> {
        // Extract the signature contents.
        let AleoSignature {
            prover_response,
            verifier_challenge,
            sigma_public_key,
            sigma_response,
        } = signature;

        // Compute G^sk_sig.
        let g_sk_sig = Self::recover_from_x_coordinate(sigma_public_key)?;

        // Compute H^sk_sig.
        let h_sk_sig = {
            // Compute public key := (H^sk_sig H^sk_prf).
            let public_key = Self::recover_from_x_coordinate(public_key)?;

            // Compute sk_prf := RO(G^sk_sig).
            let sk_prf = self.hash_to_scalar_field(&[g_sk_sig.x])?;

            // Compute H^sk_sig := public key / H^sk_prf.
            public_key - self.h_scalar_multiply(&sk_prf)?
        };

        // Compute G^sk_sig^d.
        let g_sk_sig_d = self.scalar_multiply(g_sk_sig.into_projective(), &verifier_challenge)?;

        // Compute H^sk_sig^d.
        let h_sk_sig_d = self.scalar_multiply(h_sk_sig.into_projective(), &verifier_challenge)?;

        // Compute G^r1 := G^p G^sk_sig^d.
        let g_r1 = self.g_scalar_multiply(&prover_response)? + g_sk_sig_d;

        // Compute H^r1 := H^p H^sk_sig^d.
        let h_r1 = self.h_scalar_multiply(&prover_response)? + h_sk_sig_d;

        // Compute the candidate verifier challenge.
        let candidate_verifier_challenge = {
            // Construct the hash input (G^sk_sig, G^r1, H^sk_sig, H^r1, message).
            let mut preimage = vec![];
            preimage.extend_from_slice(&g_sk_sig.x.to_field_elements()?);
            preimage.extend_from_slice(&g_r1.x.to_field_elements()?);
            preimage.extend_from_slice(&h_sk_sig.x.to_field_elements()?);
            preimage.extend_from_slice(&h_r1.x.to_field_elements()?);
            preimage.push(TE::BaseField::from(message.len() as u128));
            preimage.extend_from_slice(&message.to_field_elements()?);

            // Hash to derive the verifier challenge.
            self.hash_to_scalar_field(&preimage)?
        };

        // Compute the sigma challenge on G as G^z.
        let sigma_challenge_g = self.g_scalar_multiply(&sigma_response)?;

        // Compute the sigma challenge on H as H^z.
        let sigma_challenge_h = self.h_scalar_multiply(&sigma_response)?;

        // Compute r := r1 + r2 = p + z.
        let r = *prover_response + sigma_response;

        // Compute G^r2 := G^r / G^r1.
        let g_r2 = self.g_scalar_multiply(&r)? - g_r1;

        // Compute H^r2 := H^r / H^r1.
        let h_r2 = self.h_scalar_multiply(&r)? - h_r1;

        // Compute the candidate sigma challenge for G as (G^r2 G^sk_sig^d).
        let candidate_sigma_challenge_g = g_r2 + g_sk_sig_d;

        // Compute the candidate sigma challenge for H as (H^r2 H^sk_sig^d).
        let candidate_sigma_challenge_h = h_r2 + h_sk_sig_d;

        Ok(*verifier_challenge == candidate_verifier_challenge
            && sigma_challenge_g == candidate_sigma_challenge_g
            && sigma_challenge_h == candidate_sigma_challenge_h)
    }
}

impl<TE: TwistedEdwardsParameters> AleoSignatureScheme<TE>
where
    TE::BaseField: PoseidonDefaultParametersField,
{
    fn scalar_multiply(&self, base: TEProjective<TE>, scalar: &TE::ScalarField) -> Result<TEAffine<TE>> {
        Ok(base.mul(*scalar).into_affine())
    }

    fn g_scalar_multiply(&self, scalar: &TE::ScalarField) -> Result<TEAffine<TE>> {
        Ok(self
            .g_bases
            .iter()
            .zip_eq(from_bytes_le_to_bits_le(&scalar.to_bytes_le()?))
            .filter_map(|(base, bit)| match bit {
                true => Some(base),
                false => None,
            })
            .sum::<TEProjective<TE>>()
            .into_affine())
    }

    fn h_scalar_multiply(&self, scalar: &TE::ScalarField) -> Result<TEAffine<TE>> {
        Ok(self
            .h_bases
            .iter()
            .zip_eq(from_bytes_le_to_bits_le(&scalar.to_bytes_le()?))
            .filter_map(|(base, bit)| match bit {
                true => Some(base),
                false => None,
            })
            .sum::<TEProjective<TE>>()
            .into_affine())
    }

    fn hash_to_scalar_field(&self, input: &[TE::BaseField]) -> Result<TE::ScalarField> {
        // Use Poseidon as a random oracle.
        let output = PoseidonCryptoHash::<TE::BaseField, 4, false>::evaluate(&input)?;

        // Truncate the output to fit in the scalar field.
        let mut bits = output.to_repr().to_bits_le();
        bits.resize(<TE::ScalarField as PrimeField>::Parameters::CAPACITY as usize, false);
        let biginteger = <TE::ScalarField as PrimeField>::BigInteger::from_bits_le(&bits);

        // Output the scalar field.
        match <TE::ScalarField as PrimeField>::from_repr(biginteger) {
            Some(scalar) => Ok(scalar),
            _ => Err(anyhow!("Failed to hash input into scalar field")),
        }
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

        Err(SignatureError::Message("Failed to read the signature public key".into()).into())
    }
}

impl<TE: TwistedEdwardsParameters> From<(Vec<TEProjective<TE>>, Vec<TEProjective<TE>>)> for AleoSignatureScheme<TE> {
    fn from((g_bases, h_bases): (Vec<TEProjective<TE>>, Vec<TEProjective<TE>>)) -> Self {
        Self { g_bases, h_bases }
    }
}

impl<TE: TwistedEdwardsParameters> ToBytes for AleoSignatureScheme<TE> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        (self.g_bases.len() as u32).write_le(&mut writer)?;
        for g in &self.g_bases {
            g.into_affine().write_le(&mut writer)?;
        }

        (self.h_bases.len() as u32).write_le(&mut writer)?;
        for h in &self.h_bases {
            h.into_affine().write_le(&mut writer)?;
        }

        Ok(())
    }
}

impl<TE: TwistedEdwardsParameters> FromBytes for AleoSignatureScheme<TE> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let g_bases_length: u32 = FromBytes::read_le(&mut reader)?;
        let mut g_bases = Vec::with_capacity(g_bases_length as usize);
        for _ in 0..g_bases_length {
            let g: TEAffine<TE> = FromBytes::read_le(&mut reader)?;
            g_bases.push(g.into_projective());
        }

        let h_bases_length: u32 = FromBytes::read_le(&mut reader)?;
        let mut h_bases = Vec::with_capacity(h_bases_length as usize);
        for _ in 0..h_bases_length {
            let h: TEAffine<TE> = FromBytes::read_le(&mut reader)?;
            h_bases.push(h.into_projective());
        }

        Ok(Self { g_bases, h_bases })
    }
}

impl<F: Field, TE: TwistedEdwardsParameters + ToConstraintField<F>> ToConstraintField<F> for AleoSignatureScheme<TE> {
    #[inline]
    fn to_field_elements(&self) -> Result<Vec<F>, ConstraintFieldError> {
        Ok(Vec::new())
    }
}
