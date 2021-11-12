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
    algorithms::crypto_hash::{CryptographicSpongeVar, PoseidonSpongeGadget},
    AllocGadget,
    Boolean,
    ConditionalEqGadget,
    EncryptionGadget,
    EqGadget,
    FieldGadget,
    FpGadget,
    GroupGadget,
    Integer,
    ToBytesGadget,
    UInt8,
};
use snarkvm_algorithms::{crypto_hash::PoseidonDefaultParametersField, encryption::ECIESPoseidonEncryption};
use snarkvm_curves::{
    templates::twisted_edwards_extended::{Affine as TEAffine, Projective as TEProjective},
    AffineCurve,
    Group,
    ProjectiveCurve,
    TwistedEdwardsParameters,
};
use snarkvm_fields::{FieldParameters, PrimeField};
use snarkvm_r1cs::{ConstraintSystem, SynthesisError};
use snarkvm_utilities::{borrow::Borrow, to_bytes_le, ToBytes};

use anyhow::{anyhow, Result};
use itertools::Itertools;
use std::marker::PhantomData;

type TEAffineGadget<TE, F> = crate::curves::templates::twisted_edwards::AffineGadget<TE, F, FpGadget<F>>;

/// ECIES encryption private key gadget
#[derive(Derivative)]
#[derivative(
    Clone(bound = "TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField"),
    PartialEq(bound = "TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField"),
    Eq(bound = "TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField"),
    Debug(bound = "TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField")
)]
pub struct ECIESPoseidonEncryptionPrivateKeyGadget<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField>(
    pub Vec<UInt8>,
    PhantomData<TE>,
    PhantomData<F>,
);

impl<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField> AllocGadget<TE::ScalarField, F>
    for ECIESPoseidonEncryptionPrivateKeyGadget<TE, F>
{
    fn alloc_constant<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<TE::ScalarField>,
        CS: ConstraintSystem<F>,
    >(
        _cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let private_key = to_bytes_le![value_gen()?.borrow()].unwrap();
        Ok(ECIESPoseidonEncryptionPrivateKeyGadget(
            UInt8::constant_vec(&private_key),
            PhantomData,
            PhantomData,
        ))
    }

    fn alloc<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<TE::ScalarField>, CS: ConstraintSystem<F>>(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let private_key = to_bytes_le![value_gen()?.borrow()].unwrap();
        let bytes = UInt8::alloc_vec(cs.ns(|| "allocate the private key as bytes"), &private_key)?;
        Ok(ECIESPoseidonEncryptionPrivateKeyGadget(bytes, PhantomData, PhantomData))
    }

    fn alloc_input<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<TE::ScalarField>, CS: ConstraintSystem<F>>(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let private_key = to_bytes_le![value_gen()?.borrow()].unwrap();
        let bytes = UInt8::alloc_input_vec_le(cs.ns(|| "allocate the private key as bytes"), &private_key)?;
        Ok(ECIESPoseidonEncryptionPrivateKeyGadget(bytes, PhantomData, PhantomData))
    }
}

impl<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField> ToBytesGadget<F>
    for ECIESPoseidonEncryptionPrivateKeyGadget<TE, F>
{
    fn to_bytes<CS: ConstraintSystem<F>>(&self, mut cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        self.0.to_bytes(&mut cs.ns(|| "to_bytes"))
    }

    fn to_bytes_strict<CS: ConstraintSystem<F>>(&self, mut cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        self.0.to_bytes_strict(&mut cs.ns(|| "to_bytes_strict"))
    }
}

/// ECIES encryption randomness gadget
#[derive(Derivative)]
#[derivative(
    Clone(bound = "TE: TwistedEdwardsParameters"),
    PartialEq(bound = "TE: TwistedEdwardsParameters"),
    Eq(bound = "TE: TwistedEdwardsParameters"),
    Debug(bound = "TE: TwistedEdwardsParameters")
)]
pub struct ECIESPoseidonEncryptionRandomnessGadget<TE: TwistedEdwardsParameters>(pub Vec<UInt8>, PhantomData<TE>);

impl<TE: TwistedEdwardsParameters> AllocGadget<TE::ScalarField, TE::BaseField>
    for ECIESPoseidonEncryptionRandomnessGadget<TE>
where
    TE::BaseField: PrimeField,
{
    fn alloc_constant<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<TE::ScalarField>,
        CS: ConstraintSystem<TE::BaseField>,
    >(
        _cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let randomness = to_bytes_le![value_gen()?.borrow()].unwrap();
        Ok(ECIESPoseidonEncryptionRandomnessGadget(
            UInt8::constant_vec(&randomness),
            PhantomData,
        ))
    }

    fn alloc<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<TE::ScalarField>,
        CS: ConstraintSystem<TE::BaseField>,
    >(
        cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let randomness = to_bytes_le![value_gen()?.borrow()].unwrap();
        Ok(ECIESPoseidonEncryptionRandomnessGadget(
            UInt8::alloc_vec(cs, &randomness)?,
            PhantomData,
        ))
    }

    fn alloc_input<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<TE::ScalarField>,
        CS: ConstraintSystem<TE::BaseField>,
    >(
        cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let randomness = to_bytes_le![value_gen()?.borrow()].unwrap();
        Ok(ECIESPoseidonEncryptionRandomnessGadget(
            UInt8::alloc_input_vec_le(cs, &randomness)?,
            PhantomData,
        ))
    }
}

/// ECIES Poseidon ciphertext randomizer gadget
#[derive(Derivative)]
#[derivative(
    Clone(bound = "TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField"),
    PartialEq(bound = "TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField"),
    Eq(bound = "TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField"),
    Debug(bound = "TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField")
)]
pub struct ECIESPoseidonCiphertextRandomizerGadget<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField>(
    TEAffineGadget<TE, F>,
);

impl<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField> ECIESPoseidonCiphertextRandomizerGadget<TE, F> {
    fn recover_ciphertext_randomizer(ciphertext_randomizer: TE::BaseField) -> Result<TEAffine<TE>, SynthesisError> {
        // Recover the ciphertext randomizer group element.
        let mut first = TEAffine::<TE>::from_x_coordinate(ciphertext_randomizer, true);
        if first.is_some() && !first.unwrap().is_in_correct_subgroup_assuming_on_curve() {
            first = None;
        }
        let mut second = TEAffine::<TE>::from_x_coordinate(ciphertext_randomizer, false);
        if second.is_some() && !second.unwrap().is_in_correct_subgroup_assuming_on_curve() {
            second = None;
        }
        match first.or(second) {
            Some(randomizer) => Ok(randomizer),
            None => Err(anyhow!("The ciphertext randomizer is malformed.").into()),
        }
    }
}

impl<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField> AllocGadget<TE::BaseField, F>
    for ECIESPoseidonCiphertextRandomizerGadget<TE, F>
where
    TEAffineGadget<TE, F>: GroupGadget<TEAffine<TE>, F>,
{
    fn alloc_constant<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<TE::BaseField>, CS: ConstraintSystem<F>>(
        cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let ciphertext_randomizer = Self::recover_ciphertext_randomizer(value_gen()?.borrow().clone())?;
        Ok(Self(TEAffineGadget::<TE, F>::alloc_constant(cs, || {
            Ok(ciphertext_randomizer)
        })?))
    }

    fn alloc<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<TE::BaseField>, CS: ConstraintSystem<F>>(
        cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let ciphertext_randomizer = Self::recover_ciphertext_randomizer(value_gen()?.borrow().clone())?;
        Ok(Self(TEAffineGadget::<TE, F>::alloc_checked(cs, || {
            Ok(ciphertext_randomizer)
        })?))
    }

    fn alloc_input<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<TE::BaseField>, CS: ConstraintSystem<F>>(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let point = if let Ok(pk) = value_gen() {
            Self::recover_ciphertext_randomizer(pk.borrow().clone())?
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

impl<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField> EqGadget<F>
    for ECIESPoseidonCiphertextRandomizerGadget<TE, F>
{
}

impl<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField> ConditionalEqGadget<F>
    for ECIESPoseidonCiphertextRandomizerGadget<TE, F>
{
    fn conditional_enforce_equal<CS: ConstraintSystem<F>>(
        &self,
        cs: CS,
        other: &Self,
        condition: &Boolean,
    ) -> Result<(), SynthesisError> {
        self.0.conditional_enforce_equal(cs, &other.0, condition)
    }

    fn cost() -> usize {
        <TEAffineGadget<TE, F> as ConditionalEqGadget<F>>::cost()
    }
}

impl<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField> ToBytesGadget<F>
    for ECIESPoseidonCiphertextRandomizerGadget<TE, F>
{
    fn to_bytes<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        self.0.x.to_bytes(cs)
    }

    fn to_bytes_strict<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        self.0.x.to_bytes_strict(cs)
    }
}

/// ECIES Poseidon encryption gadget
#[derive(Derivative)]
#[derivative(
    Clone(bound = "TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField"),
    PartialEq(bound = "TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField"),
    Eq(bound = "TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField"),
    Debug(bound = "TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField")
)]
pub struct ECIESPoseidonEncryptionGadget<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField>
where
    TE::BaseField: PoseidonDefaultParametersField,
{
    encryption: ECIESPoseidonEncryption<TE>,
    f_phantom: PhantomData<F>,
}

impl<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField> AllocGadget<ECIESPoseidonEncryption<TE>, F>
    for ECIESPoseidonEncryptionGadget<TE, F>
where
    TE::BaseField: PoseidonDefaultParametersField,
{
    fn alloc_constant<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<ECIESPoseidonEncryption<TE>>,
        CS: ConstraintSystem<F>,
    >(
        _cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        Ok(Self {
            encryption: (*value_gen()?.borrow()).clone(),
            f_phantom: PhantomData,
        })
    }

    fn alloc<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<ECIESPoseidonEncryption<TE>>,
        CS: ConstraintSystem<F>,
    >(
        _cs: CS,
        _value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        unimplemented!()
    }

    fn alloc_input<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<ECIESPoseidonEncryption<TE>>,
        CS: ConstraintSystem<F>,
    >(
        _cs: CS,
        _value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        unimplemented!()
    }
}

/// ECIES Poseidon public key gadget
#[derive(Derivative)]
#[derivative(
    Clone(bound = "TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField"),
    PartialEq(bound = "TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField"),
    Eq(bound = "TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField"),
    Debug(bound = "TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField")
)]
pub struct ECIESPoseidonEncryptionPublicKeyGadget<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField>(
    TEAffineGadget<TE, F>,
);

impl<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField> AllocGadget<TEAffine<TE>, F>
    for ECIESPoseidonEncryptionPublicKeyGadget<TE, F>
where
    TEAffineGadget<TE, F>: GroupGadget<TEAffine<TE>, F>,
{
    fn alloc_constant<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<TEAffine<TE>>, CS: ConstraintSystem<F>>(
        cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let public_key = value_gen()?.borrow().clone();
        Ok(Self(TEAffineGadget::<TE, F>::alloc_constant(cs, || Ok(public_key))?))
    }

    fn alloc<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<TEAffine<TE>>, CS: ConstraintSystem<F>>(
        cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let public_key = value_gen()?.borrow().clone();
        Ok(Self(TEAffineGadget::<TE, F>::alloc_checked(cs, || Ok(public_key))?))
    }

    fn alloc_input<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<TEAffine<TE>>, CS: ConstraintSystem<F>>(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let point = if let Ok(pk) = value_gen() {
            pk.borrow().clone()
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
    for ECIESPoseidonEncryptionPublicKeyGadget<TE, F>
{
    fn conditional_enforce_equal<CS: ConstraintSystem<F>>(
        &self,
        cs: CS,
        other: &Self,
        condition: &Boolean,
    ) -> Result<(), SynthesisError> {
        self.0.conditional_enforce_equal(cs, &other.0, condition)
    }

    fn cost() -> usize {
        <TEAffineGadget<TE, F> as ConditionalEqGadget<F>>::cost()
    }
}

impl<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField> ToBytesGadget<F>
    for ECIESPoseidonEncryptionPublicKeyGadget<TE, F>
{
    fn to_bytes<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        self.0.x.to_bytes(cs)
    }

    fn to_bytes_strict<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        self.0.x.to_bytes_strict(cs)
    }
}

impl<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField> EqGadget<F>
    for ECIESPoseidonEncryptionPublicKeyGadget<TE, F>
{
}

impl<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField + PoseidonDefaultParametersField>
    EncryptionGadget<ECIESPoseidonEncryption<TE>, F> for ECIESPoseidonEncryptionGadget<TE, F>
{
    type CiphertextRandomizer = ECIESPoseidonCiphertextRandomizerGadget<TE, F>;
    type PrivateKeyGadget = ECIESPoseidonEncryptionPrivateKeyGadget<TE, F>;
    type PublicKeyCommitment = FpGadget<F>;
    type PublicKeyGadget = ECIESPoseidonEncryptionPublicKeyGadget<TE, F>;
    type ScalarRandomnessGadget = ECIESPoseidonEncryptionRandomnessGadget<TE>;

    fn check_public_key_gadget<CS: ConstraintSystem<TE::BaseField>>(
        &self,
        mut cs: CS,
        private_key: &Self::PrivateKeyGadget,
    ) -> Result<Self::PublicKeyGadget, SynthesisError> {
        let private_key_bits = private_key.0.iter().flat_map(|b| b.to_bits_le()).collect::<Vec<_>>();
        let mut public_key = <TEAffineGadget<TE, F> as GroupGadget<TEAffine<TE>, F>>::zero(cs.ns(|| "zero"))?;

        let num_powers = private_key_bits.len();

        let generator_powers: Vec<TEAffine<TE>> = {
            let mut generator_powers = Vec::new();
            let mut generator = self.encryption.generator.into_projective();
            for _ in 0..num_powers {
                generator_powers.push(generator.clone());
                generator.double_in_place();
            }
            TEProjective::<TE>::batch_normalization(&mut generator_powers);
            generator_powers.into_iter().map(|v| v.into()).collect()
        };

        public_key.scalar_multiplication(
            cs.ns(|| "check_public_key_gadget"),
            private_key_bits.iter().zip_eq(&generator_powers),
        )?;

        Ok(ECIESPoseidonEncryptionPublicKeyGadget::<TE, F>(public_key))
    }

    fn check_encryption_from_scalar_randomness<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        randomness: &Self::ScalarRandomnessGadget,
        public_key: &Self::PublicKeyGadget,
        message: &[UInt8],
    ) -> Result<(Self::CiphertextRandomizer, Vec<UInt8>, Self::PublicKeyCommitment), SynthesisError> {
        let affine_zero: TEAffineGadget<TE, F> =
            <TEAffineGadget<TE, F> as GroupGadget<TEAffine<TE>, F>>::zero(cs.ns(|| "affine zero")).unwrap();

        // Compute the ECDH value.
        let randomness_bits = randomness.0.iter().flat_map(|b| b.to_bits_le()).collect::<Vec<_>>();
        let symmetric_key = <TEAffineGadget<TE, F> as GroupGadget<TEAffine<TE>, F>>::mul_bits(
            &public_key.0,
            cs.ns(|| "compute_ecdh_value"),
            &affine_zero,
            randomness_bits.iter().copied(),
        )?
        .x;

        // Prepare the sponge.
        let params =
            <TE::BaseField as PoseidonDefaultParametersField>::get_default_poseidon_parameters(4, false).unwrap();
        let mut sponge = PoseidonSpongeGadget::<TE::BaseField>::new(cs.ns(|| "sponge"), &params);
        let domain_separator = FpGadget::alloc_constant(cs.ns(|| "domain_separator"), || {
            Ok(TE::BaseField::from_bytes_le_mod_order(b"AleoEncryption2021"))
        })?;
        sponge.absorb(cs.ns(|| "absorb"), [domain_separator, symmetric_key].iter())?;

        // Squeeze one element for the commitment randomness.
        let key_commitment =
            sponge.squeeze_field_elements(cs.ns(|| "squeeze field elements for polyMAC"), 1)?[0].clone();

        // Convert the message into bits.
        let mut bits = Vec::with_capacity(message.len() * 8);
        for byte in message.iter() {
            bits.extend_from_slice(&byte.to_bits_le());
        }
        bits.push(Boolean::Constant(true));
        // The last bit indicates the end of the actual data, which is used in decoding to
        // make sure that the length is correct.

        // Pack the bits into field elements.
        let capacity = <<TE::BaseField as PrimeField>::Parameters as FieldParameters>::CAPACITY as usize;
        let mut res = Vec::with_capacity((bits.len() + capacity - 1) / capacity);
        for (i, chunk) in bits.chunks(capacity).enumerate() {
            res.push(Boolean::le_bits_to_fp_var(
                cs.ns(|| format!("convert a bit to a field element {}", i)),
                chunk,
            )?);
        }

        // Obtain random field elements from Poseidon.
        let sponge_field_elements =
            sponge.squeeze_field_elements(cs.ns(|| "squeeze for random elements"), res.len())?;

        // Add the random field elements to the packed bits.
        for (i, sponge_field_element) in sponge_field_elements.iter().enumerate() {
            res[i].add_in_place(
                cs.ns(|| format!("add the sponge field element {}", i)),
                sponge_field_element,
            )?;
        }

        let ciphertext = res.to_bytes(cs.ns(|| "convert the masked results into bytes"))?;

        // Put the bytes of the x coordinate of the randomness group element
        // into the beginning of the ciphertext.
        let generator_gadget = TEAffineGadget::<TE, F>::alloc_constant(cs.ns(|| "alloc generator"), || {
            Ok(self.encryption.generator.clone())
        })?;
        let ciphertext_randomizer =
            ECIESPoseidonCiphertextRandomizerGadget(<TEAffineGadget<TE, F> as GroupGadget<TEAffine<TE>, F>>::mul_bits(
                &generator_gadget,
                cs.ns(|| "compute the randomness element"),
                &affine_zero,
                randomness_bits.iter().copied(),
            )?);

        Ok((ciphertext_randomizer, ciphertext, key_commitment))
    }

    fn check_encryption_from_ciphertext_randomizer<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        ciphertext_randomizer: &Self::CiphertextRandomizer,
        private_key: &Self::PrivateKeyGadget,
        message: &[UInt8],
    ) -> Result<(Vec<UInt8>, Self::PublicKeyCommitment), SynthesisError> {
        let affine_zero: TEAffineGadget<TE, F> =
            <TEAffineGadget<TE, F> as GroupGadget<TEAffine<TE>, F>>::zero(cs.ns(|| "affine zero")).unwrap();

        // Compute the symmetric key.
        let private_key_bits = private_key.0.iter().flat_map(|b| b.to_bits_le()).collect::<Vec<_>>();
        let symmetric_key = <TEAffineGadget<TE, F> as GroupGadget<TEAffine<TE>, F>>::mul_bits(
            &ciphertext_randomizer.0,
            cs.ns(|| "compute the symmetric key"),
            &affine_zero,
            private_key_bits.iter().copied(),
        )?
        .x;

        // Prepare the sponge.
        let params =
            <TE::BaseField as PoseidonDefaultParametersField>::get_default_poseidon_parameters(4, false).unwrap();
        let mut sponge = PoseidonSpongeGadget::<TE::BaseField>::new(cs.ns(|| "sponge"), &params);
        let domain_separator = FpGadget::alloc_constant(cs.ns(|| "domain_separator"), || {
            Ok(TE::BaseField::from_bytes_le_mod_order(b"AleoEncryption2021"))
        })?;
        sponge.absorb(cs.ns(|| "absorb"), [domain_separator, symmetric_key].iter())?;

        // Squeeze one element for the public key commitment randomness.
        let key_commitment =
            sponge.squeeze_field_elements(cs.ns(|| "squeeze field elements for polyMAC"), 1)?[0].clone();

        // Convert the message into bits.
        let mut bits = Vec::with_capacity(message.len() * 8);
        for byte in message.iter() {
            bits.extend_from_slice(&byte.to_bits_le());
        }
        bits.push(Boolean::Constant(true));
        // The last bit indicates the end of the actual data, which is used in decoding to
        // make sure that the length is correct.

        // Pack the bits into field elements.
        let capacity = <<TE::BaseField as PrimeField>::Parameters as FieldParameters>::CAPACITY as usize;
        let mut res = Vec::with_capacity((bits.len() + capacity - 1) / capacity);
        for (i, chunk) in bits.chunks(capacity).enumerate() {
            res.push(Boolean::le_bits_to_fp_var(
                cs.ns(|| format!("convert a bit to a field element {}", i)),
                chunk,
            )?);
        }

        // Obtain random field elements from Poseidon.
        let sponge_field_elements =
            sponge.squeeze_field_elements(cs.ns(|| "squeeze for random elements"), res.len())?;

        // Add the random field elements to the packed bits.
        for (i, sponge_field_element) in sponge_field_elements.iter().enumerate() {
            res[i].add_in_place(
                cs.ns(|| format!("add the sponge field element {}", i)),
                sponge_field_element,
            )?;
        }

        let ciphertext = res.to_bytes(cs.ns(|| "convert the masked results into bytes"))?;

        Ok((ciphertext, key_commitment))
    }
}
