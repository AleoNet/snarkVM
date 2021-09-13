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
    algorithms::crypto_hash::PoseidonCryptoHashGadget,
    bits::{Boolean, ToBytesGadget},
    integers::uint::UInt8,
    traits::{
        algorithms::SignatureGadget,
        alloc::AllocGadget,
        curves::GroupGadget,
        eq::{ConditionalEqGadget, EqGadget},
        fields::field::FieldGadget,
        select::CondSelectGadget,
    },
    CryptoHashGadget,
    FpGadget,
    ToBitsLEGadget,
    ToConstraintFieldGadget,
};
use snarkvm_algorithms::{
    crypto_hash::PoseidonDefaultParametersField,
    signature::{AleoSignature, AleoSignatureScheme},
};
use snarkvm_curves::{templates::twisted_edwards_extended::Affine as TEAffine, AffineCurve, TwistedEdwardsParameters};
use snarkvm_fields::{FieldParameters, PrimeField};
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSystem};
use snarkvm_utilities::{FromBytes, ToBytes};

use anyhow::{anyhow, Result};
use itertools::Itertools;
use std::{borrow::Borrow, marker::PhantomData};

type TEAffineGadget<TE, F> = crate::curves::templates::twisted_edwards::AffineGadget<TE, F, FpGadget<F>>;

#[derive(Derivative)]
#[derivative(
    Clone(bound = "TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField"),
    PartialEq(bound = "TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField"),
    Eq(bound = "TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField"),
    Debug(bound = "TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField")
)]
pub struct AleoSignaturePublicKeyGadget<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField>(
    TEAffineGadget<TE, F>,
);

impl<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField> AleoSignaturePublicKeyGadget<TE, F> {
    fn recover_from_x_coordinate(x_coordinate: TE::BaseField) -> Result<TEAffine<TE>> {
        if let Some(element) = TEAffine::<TE>::from_x_coordinate(x_coordinate, true) {
            if element.is_in_correct_subgroup_assuming_on_curve() {
                return Ok(element);
            }
        }

        if let Some(element) = TEAffine::<TE>::from_x_coordinate(x_coordinate, false) {
            if element.is_in_correct_subgroup_assuming_on_curve() {
                return Ok(element);
            }
        }

        Err(anyhow!("Failed to read the signature public key"))
    }
}

impl<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField> AllocGadget<TE::BaseField, F>
    for AleoSignaturePublicKeyGadget<TE, F>
{
    fn alloc_constant<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<TE::BaseField>, CS: ConstraintSystem<F>>(
        cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let public_key = Self::recover_from_x_coordinate(value_gen()?.borrow().clone())?;
        Ok(Self(TEAffineGadget::<TE, F>::alloc_constant(cs, || Ok(public_key))?))
    }

    fn alloc<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<TE::BaseField>, CS: ConstraintSystem<F>>(
        cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let public_key = Self::recover_from_x_coordinate(value_gen()?.borrow().clone())?;
        Ok(Self(TEAffineGadget::<TE, F>::alloc_checked(cs, || Ok(public_key))?))
    }

    fn alloc_input<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<TE::BaseField>, CS: ConstraintSystem<F>>(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let point = if let Ok(pk) = value_gen() {
            Self::recover_from_x_coordinate(pk.borrow().clone())?
        } else {
            TEAffine::<TE>::default()
        };

        let x_coordinate_gadget =
            FpGadget::<TE::BaseField>::alloc_input(cs.ns(|| "input x coordinate"), || Ok(point.x))?;
        let allocated_gadget =
            TEAffineGadget::<TE, F>::alloc_checked(cs.ns(|| "input the allocated point"), || Ok(point.clone()))?;

        allocated_gadget
            .x
            .enforce_equal(cs.ns(|| "check x consistency"), &x_coordinate_gadget)?;

        Ok(Self(allocated_gadget))
    }
}

impl<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField> ConditionalEqGadget<F>
    for AleoSignaturePublicKeyGadget<TE, F>
{
    #[inline]
    fn conditional_enforce_equal<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        other: &Self,
        condition: &Boolean,
    ) -> Result<(), SynthesisError> {
        self.0
            .conditional_enforce_equal(&mut cs.ns(|| "conditional_enforce_equal"), &other.0, condition)?;
        Ok(())
    }

    fn cost() -> usize {
        <TEAffineGadget<TE, F> as ConditionalEqGadget<F>>::cost()
    }
}

impl<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField> EqGadget<F> for AleoSignaturePublicKeyGadget<TE, F> {}

impl<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField> ToBytesGadget<F>
    for AleoSignaturePublicKeyGadget<TE, F>
{
    fn to_bytes<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        self.0.x.to_bytes(cs)
    }

    fn to_bytes_strict<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        self.0.x.to_bytes_strict(cs)
    }
}

#[derive(Derivative)]
#[derivative(
    Clone(bound = "TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField"),
    PartialEq(bound = "TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField"),
    Eq(bound = "TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField"),
    Debug(bound = "TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField")
)]
pub struct AleoSignatureGadget<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField> {
    pub(crate) prover_response: FpGadget<F>,
    pub(crate) verifier_challenge: FpGadget<F>,
    pub(crate) sigma_public_key: TEAffineGadget<TE, F>,
    pub(crate) sigma_response: FpGadget<F>,
}

impl<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField> AllocGadget<AleoSignature<TE>, F>
    for AleoSignatureGadget<TE, F>
{
    fn alloc<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<AleoSignature<TE>>, CS: ConstraintSystem<F>>(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let value = value_gen()?;
        let signature = value.borrow().clone();

        // TODO (raychu86): Check that this conversion is valid.
        //      This will work for EdwardsBls Fr and Bls12_377 Fr because they are both represented with Fp256.

        // Cast <G as Group>::ScalarField as F.
        let prover_response: F = FromBytes::read_le(&signature.prover_response.to_bytes_le()?[..])?;
        let verifier_challenge: F = FromBytes::read_le(&signature.verifier_challenge.to_bytes_le()?[..])?;
        let sigma_response: F = FromBytes::read_le(&signature.sigma_response.to_bytes_le()?[..])?;

        let prover_response = FpGadget::<F>::alloc(cs.ns(|| "alloc_prover_response"), || Ok(&prover_response))?;
        let verifier_challenge =
            FpGadget::<F>::alloc(cs.ns(|| "alloc_verifier_challenge"), || Ok(&verifier_challenge))?;
        let sigma_public_key =
            TEAffineGadget::<TE, F>::alloc(cs.ns(|| "alloc_sigma_public_key"), || Ok(signature.root_public_key()?))?;
        let sigma_response = FpGadget::<F>::alloc(cs.ns(|| "alloc_sigma_response"), || Ok(&sigma_response))?;

        Ok(Self {
            prover_response,
            verifier_challenge,
            sigma_public_key,
            sigma_response,
        })
    }

    fn alloc_constant<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<AleoSignature<TE>>,
        CS: ConstraintSystem<F>,
    >(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let value = value_gen()?;
        let signature = value.borrow().clone();

        // Cast <G as Group>::ScalarField as F.
        let prover_response: F = FromBytes::read_le(&signature.prover_response.to_bytes_le()?[..])?;
        let verifier_challenge: F = FromBytes::read_le(&signature.verifier_challenge.to_bytes_le()?[..])?;
        let sigma_response: F = FromBytes::read_le(&signature.sigma_response.to_bytes_le()?[..])?;

        let prover_response =
            FpGadget::<F>::alloc_constant(cs.ns(|| "alloc_constant_prover_response"), || Ok(&prover_response))?;
        let verifier_challenge = FpGadget::<F>::alloc_constant(cs.ns(|| "alloc_constant_verifier_challenge"), || {
            Ok(&verifier_challenge)
        })?;
        let sigma_public_key =
            TEAffineGadget::<TE, F>::alloc_constant(cs.ns(|| "alloc_constant_sigma_public_key"), || {
                Ok(signature.root_public_key()?)
            })?;
        let sigma_response =
            FpGadget::<F>::alloc_constant(cs.ns(|| "alloc_constant_sigma_response"), || Ok(&sigma_response))?;

        Ok(Self {
            prover_response,
            verifier_challenge,
            sigma_public_key,
            sigma_response,
        })
    }

    fn alloc_input<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<AleoSignature<TE>>, CS: ConstraintSystem<F>>(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let value = value_gen()?;
        let signature = value.borrow().clone();

        // Cast <G as Group>::ScalarField as F.
        let prover_response: F = FromBytes::read_le(&signature.prover_response.to_bytes_le()?[..])?;
        let verifier_challenge: F = FromBytes::read_le(&signature.verifier_challenge.to_bytes_le()?[..])?;
        let sigma_response: F = FromBytes::read_le(&signature.sigma_response.to_bytes_le()?[..])?;

        let prover_response =
            FpGadget::<F>::alloc_input(cs.ns(|| "alloc_input_prover_response"), || Ok(&prover_response))?;
        let verifier_challenge =
            FpGadget::<F>::alloc_input(cs.ns(|| "alloc_input_verifier_challenge"), || Ok(&verifier_challenge))?;
        let sigma_public_key = TEAffineGadget::<TE, F>::alloc_input(cs.ns(|| "alloc_input_sigma_public_key"), || {
            Ok(signature.root_public_key()?)
        })?;
        let sigma_response =
            FpGadget::<F>::alloc_input(cs.ns(|| "alloc_input_sigma_response"), || Ok(&sigma_response))?;

        Ok(Self {
            prover_response,
            verifier_challenge,
            sigma_public_key,
            sigma_response,
        })
    }
}

impl<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField> ConditionalEqGadget<F> for AleoSignatureGadget<TE, F> {
    #[inline]
    fn conditional_enforce_equal<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        other: &Self,
        condition: &Boolean,
    ) -> Result<(), SynthesisError> {
        self.prover_response.conditional_enforce_equal(
            &mut cs.ns(|| "prover_response_conditional_enforce_equal"),
            &other.prover_response,
            condition,
        )?;
        self.verifier_challenge.conditional_enforce_equal(
            &mut cs.ns(|| "verifier_challenge_conditional_enforce_equal"),
            &other.verifier_challenge,
            condition,
        )?;
        self.sigma_public_key.conditional_enforce_equal(
            &mut cs.ns(|| "sigma_public_key_conditional_enforce_equal"),
            &other.sigma_public_key,
            condition,
        )?;
        self.sigma_response.conditional_enforce_equal(
            &mut cs.ns(|| "sigma_response_conditional_enforce_equal"),
            &other.sigma_response,
            condition,
        )?;
        Ok(())
    }

    fn cost() -> usize {
        <FpGadget<F> as ConditionalEqGadget<F>>::cost() * 2
    }
}

impl<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField> EqGadget<F> for AleoSignatureGadget<TE, F> {}

impl<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField> ToBytesGadget<F> for AleoSignatureGadget<TE, F> {
    fn to_bytes<CS: ConstraintSystem<F>>(&self, mut cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        let mut result = Vec::new();

        result.extend(
            self.prover_response
                .to_bytes(&mut cs.ns(|| "prover_response_to_bytes"))?,
        );
        result.extend(
            self.verifier_challenge
                .to_bytes(&mut cs.ns(|| "verifier_challenge_to_bytes"))?,
        );
        result.extend(
            self.sigma_public_key
                .to_bytes(&mut cs.ns(|| "sigma_public_key_to_bytes"))?,
        );
        result.extend(self.sigma_response.to_bytes(&mut cs.ns(|| "sigma_response_to_bytes"))?);

        Ok(result)
    }

    fn to_bytes_strict<CS: ConstraintSystem<F>>(&self, mut cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        let mut result = Vec::new();

        result.extend(
            self.prover_response
                .to_bytes_strict(&mut cs.ns(|| "prover_response_to_bytes_strict"))?,
        );
        result.extend(
            self.verifier_challenge
                .to_bytes_strict(&mut cs.ns(|| "verifier_challenge_to_bytes_strict"))?,
        );
        result.extend(
            self.sigma_public_key
                .to_bytes_strict(&mut cs.ns(|| "sigma_public_key_to_bytes_strict"))?,
        );
        result.extend(
            self.sigma_response
                .to_bytes_strict(&mut cs.ns(|| "sigma_response_to_bytes_strict"))?,
        );

        Ok(result)
    }
}

pub struct AleoSignatureSchemeGadget<
    TE: TwistedEdwardsParameters<BaseField = F>,
    F: PrimeField + PoseidonDefaultParametersField,
> {
    pub(crate) signature: AleoSignatureScheme<TE>,
    pub(crate) _engine: PhantomData<F>,
}

impl<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField + PoseidonDefaultParametersField>
    AllocGadget<AleoSignatureScheme<TE>, F> for AleoSignatureSchemeGadget<TE, F>
{
    fn alloc_constant<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<AleoSignatureScheme<TE>>,
        CS: ConstraintSystem<F>,
    >(
        _cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        Ok(Self {
            signature: (*value_gen()?.borrow()).clone(),
            _engine: PhantomData,
        })
    }

    fn alloc<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<AleoSignatureScheme<TE>>, CS: ConstraintSystem<F>>(
        _cs: CS,
        _value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        unimplemented!()
    }

    fn alloc_input<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<AleoSignatureScheme<TE>>,
        CS: ConstraintSystem<F>,
    >(
        _cs: CS,
        _value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        unimplemented!()
    }
}

impl<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField + PoseidonDefaultParametersField>
    SignatureGadget<AleoSignatureScheme<TE>, F> for AleoSignatureSchemeGadget<TE, F>
{
    type PublicKeyGadget = AleoSignaturePublicKeyGadget<TE, F>;
    type SignatureGadget = AleoSignatureGadget<TE, F>;

    fn verify<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        public_key: &Self::PublicKeyGadget,
        message: &[UInt8],
        signature: &Self::SignatureGadget,
    ) -> Result<Boolean, SynthesisError> {
        // Prepare the zero element in affine form for use.
        let zero_affine: TEAffineGadget<TE, F> =
            <TEAffineGadget<TE, F> as GroupGadget<TEAffine<TE>, F>>::zero(cs.ns(|| "affine zero"))?;

        // Compute G^sk_sig.
        let g_sk_sig = &signature.sigma_public_key;

        // Compute H^sk_sig.
        let h_sk_sig = {
            // Compute sk_prf := RO(G^sk_sig).
            let sk_prf = {
                // Compute the hash of G^sk_sig on the base field.
                let output = PoseidonCryptoHashGadget::<F, 4, false>::check_evaluation_gadget(
                    cs.ns(|| "Poseidon of G^sk_sig"),
                    &[g_sk_sig.x.clone()],
                )?;

                // Truncate the output to fit the scalar field.
                let mut sk_prf_bits = output.to_bits_le(cs.ns(|| "Convert the output into bits"))?;
                sk_prf_bits.resize(
                    <TE::ScalarField as PrimeField>::Parameters::CAPACITY as usize,
                    Boolean::Constant(false),
                );
                sk_prf_bits.push(Boolean::Constant(false)); // Append one 0 bit to match MODULUS_BITS size.
                sk_prf_bits
            };

            // Compute H^sk_prf.
            let h_sk_prf = {
                let mut h_sk_prf = zero_affine.clone();
                for (i, (base, bit)) in self.signature.h_bases.iter().zip_eq(sk_prf).enumerate() {
                    let added = h_sk_prf.add_constant(cs.ns(|| format!("add_h_sk_prf_{}", i)), base)?;

                    h_sk_prf = TEAffineGadget::<TE, F>::conditionally_select(
                        cs.ns(|| format!("cond_select_h_sk_prf_{}", i)),
                        &bit,
                        &added,
                        &h_sk_prf,
                    )?;
                }
                h_sk_prf
            };

            // Compute H^sk_sig := public key / H^sk_prf.
            <TEAffineGadget<TE, F> as GroupGadget<TEAffine<TE>, F>>::sub(
                &public_key.0,
                cs.ns(|| "public key H^-sk_prf"),
                &h_sk_prf,
            )?
        };

        // Prepare p, by converting the prover response to bits.
        let p = {
            let mut p_bits = signature
                .prover_response
                .to_bits_le_strict(cs.ns(|| "prover_response to_bits_le_strict"))?;

            // Truncate p to fit the scalar field.
            p_bits.resize(
                <TE::ScalarField as PrimeField>::Parameters::MODULUS_BITS as usize,
                Boolean::Constant(false),
            );
            p_bits
        };

        // Compute G^p.
        let g_p = {
            let mut g_p = zero_affine.clone();
            for (i, (base, bit)) in self.signature.g_bases.iter().zip_eq(p.clone()).enumerate() {
                let added = g_p.add_constant(cs.ns(|| format!("add_g_p_{}", i)), base)?;

                g_p = TEAffineGadget::<TE, F>::conditionally_select(
                    cs.ns(|| format!("cond_select_g_p_{}", i)),
                    &bit,
                    &added,
                    &g_p,
                )?;
            }
            g_p
        };

        // Compute H^p.
        let h_p = {
            let mut h_p = zero_affine.clone();
            for (i, (base, bit)) in self.signature.h_bases.iter().zip_eq(p).enumerate() {
                let added = h_p.add_constant(cs.ns(|| format!("add_h_p_{}", i)), base)?;

                h_p = TEAffineGadget::<TE, F>::conditionally_select(
                    cs.ns(|| format!("cond_select_h_p_{}", i)),
                    &bit,
                    &added,
                    &h_p,
                )?;
            }
            h_p
        };

        // Prepare d, by converting the verifier challenge to bits.
        let d = {
            let mut d_bits = signature
                .verifier_challenge
                .to_bits_le_strict(cs.ns(|| "verifier_challenge to_bits_le_strict"))?;

            // Truncate d to fit the scalar field.
            d_bits.resize(
                <TE::ScalarField as PrimeField>::Parameters::MODULUS_BITS as usize,
                Boolean::Constant(false),
            );
            d_bits
        };

        // Compute G^sk_sig^d.
        let g_sk_sig_d = <TEAffineGadget<TE, F> as GroupGadget<TEAffine<TE>, F>>::mul_bits(
            &g_sk_sig,
            cs.ns(|| "G^sk_sig^d"),
            &zero_affine,
            d.clone().into_iter(),
        )?;

        // Compute H^sk_sig^d.
        let h_sk_sig_d = <TEAffineGadget<TE, F> as GroupGadget<TEAffine<TE>, F>>::mul_bits(
            &h_sk_sig,
            cs.ns(|| "H^sk_sig^d"),
            &zero_affine,
            d.into_iter(),
        )?;

        // Compute G^r1 := G^p G^sk_sig^d.
        let g_r1 = <TEAffineGadget<TE, F> as GroupGadget<TEAffine<TE>, F>>::add(
            &g_p,
            cs.ns(|| "G^r1 := G^p G^sk_sig^d"),
            &g_sk_sig_d,
        )?;

        // Compute H^r1 := H^p H^sk_sig^d.
        let h_r1 = <TEAffineGadget<TE, F> as GroupGadget<TEAffine<TE>, F>>::add(
            &h_p,
            cs.ns(|| "H^r1 := H^p H^sk_sig^d"),
            &h_sk_sig_d,
        )?;

        // Compute the candidate verifier challenge.
        let candidate_verifier_challenge = {
            // Construct the hash input (G^sk_sig, G^r1, H^sk_sig, H^r1, message).
            let mut preimage = Vec::new();
            preimage.extend_from_slice(
                &g_sk_sig
                    .x
                    .to_constraint_field(cs.ns(|| "G^sk_sig to constraint field"))?,
            );
            preimage.extend_from_slice(&g_r1.x.to_constraint_field(cs.ns(|| "G^r1 to constraint field"))?);
            preimage.extend_from_slice(
                &h_sk_sig
                    .x
                    .to_constraint_field(cs.ns(|| "H^sk_sig to constraint field"))?,
            );
            preimage.extend_from_slice(&h_r1.x.to_constraint_field(cs.ns(|| "H^r1 to constraint field"))?);
            preimage.push(FpGadget::<F>::Constant(F::from(message.len() as u128)));
            preimage.extend_from_slice(&message.to_constraint_field(cs.ns(|| "convert message into field elements"))?);

            // Compute the hash of the preimage on the base field.
            let hash = PoseidonCryptoHashGadget::<F, 4, false>::check_evaluation_gadget(
                cs.ns(|| "Poseidon of preimage"),
                &preimage,
            )?;

            // Truncate the output to fit the scalar field.
            let mut hash_bits = hash.to_bits_le(cs.ns(|| "convert the hash into bits"))?;
            hash_bits.resize(
                <TE::ScalarField as PrimeField>::Parameters::CAPACITY as usize,
                Boolean::Constant(false),
            );

            // Output the verifier challenge.
            Boolean::le_bits_to_fp_var(cs.ns(|| "obtain the truncated hash"), &hash_bits)?
        };

        // Prepare z, by converting the sigma response to bits.
        let z = {
            let mut z_bits = signature
                .sigma_response
                .to_bits_le_strict(cs.ns(|| "sigma_response to_bits_le_strict"))?;

            // Truncate z to fit the scalar field.
            z_bits.resize(
                <TE::ScalarField as PrimeField>::Parameters::MODULUS_BITS as usize,
                Boolean::Constant(false),
            );
            z_bits
        };

        // Compute the sigma challenge on G as G^z.
        let sigma_challenge_g = {
            let mut g_z = zero_affine.clone();
            for (i, (base, bit)) in self.signature.g_bases.iter().zip_eq(z.clone()).enumerate() {
                let added = g_z.add_constant(cs.ns(|| format!("add_g_z_{}", i)), base)?;

                g_z = TEAffineGadget::<TE, F>::conditionally_select(
                    cs.ns(|| format!("cond_select_g_z_{}", i)),
                    &bit,
                    &added,
                    &g_z,
                )?;
            }
            g_z
        };

        // Compute the sigma challenge on H as H^z.
        let sigma_challenge_h = {
            let mut h_z = zero_affine.clone();
            for (i, (base, bit)) in self.signature.h_bases.iter().zip_eq(z).enumerate() {
                let added = h_z.add_constant(cs.ns(|| format!("add_h_z_{}", i)), base)?;

                h_z = TEAffineGadget::<TE, F>::conditionally_select(
                    cs.ns(|| format!("cond_select_h_z_{}", i)),
                    &bit,
                    &added,
                    &h_z,
                )?;
            }
            h_z
        };

        // Compute r := r1 + r2 = p + z.
        let r = {
            let r = signature
                .prover_response
                .add(cs.ns(|| "p + z"), &signature.sigma_response)?;

            // Truncate r to fit the scalar field.
            let mut r_bits = r.to_bits_le_strict(cs.ns(|| "r to_bits_le_strict"))?;
            r_bits.resize(
                <TE::ScalarField as PrimeField>::Parameters::MODULUS_BITS as usize,
                Boolean::Constant(false),
            );
            r_bits
        };

        // Compute G^r.
        let g_r = {
            let mut g_z = zero_affine.clone();
            for (i, (base, bit)) in self.signature.g_bases.iter().zip_eq(r.clone()).enumerate() {
                let added = g_z.add_constant(cs.ns(|| format!("add_g_r_{}", i)), base)?;

                g_z = TEAffineGadget::<TE, F>::conditionally_select(
                    cs.ns(|| format!("cond_select_g_r_{}", i)),
                    &bit,
                    &added,
                    &g_z,
                )?;
            }
            g_z
        };

        // Compute H^r.
        let h_r = {
            let mut h_z = zero_affine.clone();
            for (i, (base, bit)) in self.signature.h_bases.iter().zip_eq(r).enumerate() {
                let added = h_z.add_constant(cs.ns(|| format!("add_h_r_{}", i)), base)?;

                h_z = TEAffineGadget::<TE, F>::conditionally_select(
                    cs.ns(|| format!("cond_select_h_r_{}", i)),
                    &bit,
                    &added,
                    &h_z,
                )?;
            }
            h_z
        };

        // Compute G^r2 := G^r / G^r1.
        let g_r2 = <TEAffineGadget<TE, F> as GroupGadget<TEAffine<TE>, F>>::sub(&g_r, cs.ns(|| "G^r G^-r1"), &g_r1)?;

        // Compute H^r2 := H^r / H^r1.
        let h_r2 = <TEAffineGadget<TE, F> as GroupGadget<TEAffine<TE>, F>>::sub(&h_r, cs.ns(|| "H^r H^-r1"), &h_r1)?;

        // Compute the candidate sigma challenge for G as (G^r2 G^sk_sig^d).
        let candidate_sigma_challenge_g = <TEAffineGadget<TE, F> as GroupGadget<TEAffine<TE>, F>>::add(
            &g_r2,
            cs.ns(|| "G^r2 G^sk_sig^d"),
            &g_sk_sig_d,
        )?;

        // Compute the candidate sigma challenge for H as (H^r2 H^sk_sig^d).
        let candidate_sigma_challenge_h = <TEAffineGadget<TE, F> as GroupGadget<TEAffine<TE>, F>>::add(
            &h_r2,
            cs.ns(|| "H^r2 H^sk_sig^d"),
            &h_sk_sig_d,
        )?;

        // Check the verifier challenge equals.
        let verifier_challenge_equals = signature
            .verifier_challenge
            .is_eq(cs.ns(|| "Check verifier challenge"), &candidate_verifier_challenge)?;

        // Check the sigma challenge for G equals.
        let sigma_challenge_g_equals =
            sigma_challenge_g.is_eq(cs.ns(|| "Check sigma challenge for G"), &candidate_sigma_challenge_g)?;

        // Check the sigma challenge for H equals.
        let sigma_challenge_h_equals =
            sigma_challenge_h.is_eq(cs.ns(|| "Check sigma challenge for H"), &candidate_sigma_challenge_h)?;

        // Execute equality checks.
        let first_equality_check =
            Boolean::and(cs.ns(|| "a ^ b"), &verifier_challenge_equals, &sigma_challenge_g_equals)?;
        Ok(Boolean::and(
            cs.ns(|| "b ^ c"),
            &first_equality_check,
            &sigma_challenge_h_equals,
        )?)
    }
}
