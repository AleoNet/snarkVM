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

use snarkvm_curves::AffineCurve;
use snarkvm_fields::{Field, PrimeField};
use snarkvm_utilities::{FromBytes, ToBytes};

use anyhow::Result;
use rand::{CryptoRng, Rng};
use std::{fmt::Debug, hash::Hash};

pub trait SignatureScheme: Sized + Debug + Clone + Eq + Send + Sync {
    type Parameters: Clone + Debug + Eq;
    type PublicKey: Clone + Debug + Default + ToBytes + FromBytes + Hash + Eq + Send + Sync;
    type PrivateKey: Clone + Debug + Default + ToBytes + FromBytes + PartialEq + Eq;
    type Signature: Copy + Clone + Debug + Default + ToBytes + FromBytes + Send + Sync + PartialEq + Eq;

    fn setup(message: &str) -> Self;

    fn parameters(&self) -> &Self::Parameters;

    fn generate_private_key<R: Rng + CryptoRng>(&self, rng: &mut R) -> Self::PrivateKey;

    fn generate_public_key(&self, private_key: &Self::PrivateKey) -> Self::PublicKey;

    fn sign<R: Rng + CryptoRng>(
        &self,
        private_key: &Self::PrivateKey,
        message: &[bool],
        rng: &mut R,
    ) -> Result<Self::Signature>;

    fn verify(&self, public_key: &Self::PublicKey, message: &[bool], signature: &Self::Signature) -> Result<bool>;
}

pub trait SignatureSchemeOperations {
    type AffineCurve: AffineCurve<BaseField = Self::BaseField>;
    type BaseField: Field;
    type ScalarField: PrimeField;
    type Signature: Clone + Debug + Default + ToBytes + FromBytes + PartialEq + Eq;

    fn pk_sig(signature: &Self::Signature) -> Result<Self::AffineCurve>;
    fn pr_sig(signature: &Self::Signature) -> Result<Self::AffineCurve>;
    fn g_scalar_multiply(&self, scalar: &Self::ScalarField) -> <Self::AffineCurve as AffineCurve>::Projective;
    fn hash_to_scalar_field(&self, input: &[Self::BaseField]) -> Self::ScalarField;
}
