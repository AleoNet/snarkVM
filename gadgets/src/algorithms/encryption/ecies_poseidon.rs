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
use itertools::Itertools;
use snarkvm_algorithms::{crypto_hash::PoseidonDefaultParametersField, encryption::ECIESPoseidonEncryption};
use snarkvm_curves::{
    templates::twisted_edwards_extended::{Affine as TEAffine, Projective as TEProjective},
    AffineCurve,
    Group,
    ProjectiveCurve,
    TwistedEdwardsParameters,
};
use snarkvm_fields::PrimeField;
use snarkvm_r1cs::{ConstraintSystem, SynthesisError};
use snarkvm_utilities::{borrow::Borrow, to_bytes_le, ToBytes};
use std::marker::PhantomData;

type TEAffineGadget<TE, F> = crate::curves::templates::twisted_edwards::AffineGadget<TE, F, FpGadget<F>>;

/// Group encryption private key gadget
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
        cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let private_key = to_bytes_le![value_gen()?.borrow()].unwrap();
        Ok(ECIESPoseidonEncryptionPrivateKeyGadget(
            UInt8::alloc_vec(cs, &private_key)?,
            PhantomData,
            PhantomData,
        ))
    }

    fn alloc_input<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<TE::ScalarField>, CS: ConstraintSystem<F>>(
        cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let private_key = to_bytes_le![value_gen()?.borrow()].unwrap();
        Ok(ECIESPoseidonEncryptionPrivateKeyGadget(
            UInt8::alloc_input_vec_le(cs, &private_key)?,
            PhantomData,
            PhantomData,
        ))
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

/// Group encryption randomness gadget
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

/// Group encryption blinding exponents gadget
#[derive(Derivative)]
#[derivative(
    Clone(bound = "TE: TwistedEdwardsParameters"),
    PartialEq(bound = "TE: TwistedEdwardsParameters"),
    Eq(bound = "TE: TwistedEdwardsParameters"),
    Debug(bound = "TE: TwistedEdwardsParameters")
)]
pub struct ECIESPoseidonEncryptionWitnessGadget<TE: TwistedEdwardsParameters>(pub PhantomData<TE>);

impl<TE: TwistedEdwardsParameters> AllocGadget<Vec<()>, TE::BaseField> for ECIESPoseidonEncryptionWitnessGadget<TE> {
    fn alloc_constant<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<Vec<()>>,
        CS: ConstraintSystem<TE::BaseField>,
    >(
        _cs: CS,
        _value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        Ok(Self { 0: PhantomData })
    }

    fn alloc<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<Vec<()>>, CS: ConstraintSystem<TE::BaseField>>(
        _cs: CS,
        _value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        Ok(Self { 0: PhantomData })
    }

    fn alloc_input<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<Vec<()>>,
        CS: ConstraintSystem<TE::BaseField>,
    >(
        _cs: CS,
        _value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        Ok(Self { 0: PhantomData })
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
pub struct ECIESPoseidonEncryptionGadget<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField> {
    encryption: ECIESPoseidonEncryption<TE>,
    f_phantom: PhantomData<F>,
}

impl<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField> AllocGadget<ECIESPoseidonEncryption<TE>, F>
    for ECIESPoseidonEncryptionGadget<TE, F>
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
    fn alloc_constant<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<TEAffine<TE>>,
        CS: ConstraintSystem<TE::BaseField>,
    >(
        cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        Ok(Self {
            0: TEAffineGadget::<TE, F>::alloc_constant(cs, value_gen)?,
        })
    }

    fn alloc<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<TEAffine<TE>>,
        CS: ConstraintSystem<TE::BaseField>,
    >(
        cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        Ok(Self {
            0: TEAffineGadget::<TE, F>::alloc(cs, value_gen)?,
        })
    }

    fn alloc_input<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<TEAffine<TE>>,
        CS: ConstraintSystem<TE::BaseField>,
    >(
        cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        Ok(Self {
            0: TEAffineGadget::<TE, F>::alloc_input(cs, value_gen)?,
        })
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
        self.0.to_bytes(cs)
    }

    fn to_bytes_strict<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        self.0.to_bytes_strict(cs)
    }
}

impl<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField> EqGadget<F>
    for ECIESPoseidonEncryptionPublicKeyGadget<TE, F>
{
}

impl<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField + PoseidonDefaultParametersField>
    EncryptionGadget<ECIESPoseidonEncryption<TE>, F> for ECIESPoseidonEncryptionGadget<TE, F>
{
    type CiphertextGadget = Vec<FpGadget<F>>;
    type EncryptionWitnessGadget = ECIESPoseidonEncryptionWitnessGadget<TE>;
    type PlaintextGadget = Vec<FpGadget<F>>;
    type PrivateKeyGadget = ECIESPoseidonEncryptionPrivateKeyGadget<TE, F>;
    type PublicKeyGadget = ECIESPoseidonEncryptionPublicKeyGadget<TE, F>;
    type RandomnessGadget = ECIESPoseidonEncryptionRandomnessGadget<TE>;

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

        Ok(ECIESPoseidonEncryptionPublicKeyGadget::<TE, F> { 0: public_key })
    }

    fn check_encryption_gadget<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        randomness: &Self::RandomnessGadget,
        public_key: &Self::PublicKeyGadget,
        input: &Self::PlaintextGadget,
        _encryption_witness: &Self::EncryptionWitnessGadget,
    ) -> Result<Self::CiphertextGadget, SynthesisError> {
        let zero: TEAffineGadget<TE, F> =
            <TEAffineGadget<TE, F> as GroupGadget<TEAffine<TE>, F>>::zero(cs.ns(|| "zero")).unwrap();

        let randomness_bits = randomness.0.iter().flat_map(|b| b.to_bits_le()).collect::<Vec<_>>();
        let ecdh_value = <TEAffineGadget<TE, F> as GroupGadget<TEAffine<TE>, F>>::mul_bits(
            &public_key.0,
            cs.ns(|| "compute_ecdh_value"),
            &zero,
            randomness_bits.iter().copied(),
        )?;

        let params =
            <TE::BaseField as PoseidonDefaultParametersField>::get_default_poseidon_parameters(4, false).unwrap();
        let mut sponge = PoseidonSpongeGadget::<TE::BaseField>::new(cs.ns(|| "sponge"), &params);
        sponge.absorb(cs.ns(|| "absorb"), [ecdh_value.x].iter())?;

        let mut results = sponge.squeeze_field_elements(cs.ns(|| "squeeze"), input.len())?;
        for (i, elem) in input.iter().enumerate() {
            results[i].add_in_place(cs.ns(|| format!("encryption_{}", i)), elem)?;
        }

        Ok(results)
    }
}
