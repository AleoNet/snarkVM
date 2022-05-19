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

#![forbid(unsafe_code)]
#![allow(clippy::too_many_arguments)]

pub mod account;
pub use account::*;

pub mod program;
pub use program::*;

pub mod testnet3;
pub use testnet3::*;

use snarkvm_curves::{AffineCurve, ProjectiveCurve, TwistedEdwardsParameters};
use snarkvm_fields::traits::*;

use anyhow::Result;
use core::{fmt, hash};

pub trait Network: Copy + Clone + fmt::Debug + Eq + PartialEq + hash::Hash {
    type Affine: AffineCurve<
        BaseField = Self::Field,
        ScalarField = Self::Scalar,
        Coordinates = (Self::Field, Self::Field),
    >;
    type AffineParameters: TwistedEdwardsParameters<BaseField = Self::Field>;
    type Projective: ProjectiveCurve<Affine = Self::Affine, BaseField = Self::Field, ScalarField = Self::Scalar>;
    type Field: PrimeField + Copy;
    type Scalar: PrimeField + Copy;

    /// The maximum number of bytes allowed in a string.
    const NUM_STRING_BYTES: u32;

    /// A helper method to recover the y-coordinate given the x-coordinate for
    /// a twisted Edwards point, returning the affine curve point.
    fn affine_from_x_coordinate(x: Self::Field) -> Result<Self::Affine>;

    /// Returns a BHP commitment for the given (up to) 256-bit input and randomizer.
    fn commit_bhp256(input: &[bool], randomizer: &Self::Scalar) -> Result<Self::Field>;

    /// Returns a BHP commitment for the given (up to) 512-bit input and randomizer.
    fn commit_bhp512(input: &[bool], randomizer: &Self::Scalar) -> Result<Self::Field>;

    /// Returns a BHP commitment for the given (up to) 768-bit input and randomizer.
    fn commit_bhp768(input: &[bool], randomizer: &Self::Scalar) -> Result<Self::Field>;

    /// Returns a BHP commitment for the given (up to) 1024-bit input and randomizer.
    fn commit_bhp1024(input: &[bool], randomizer: &Self::Scalar) -> Result<Self::Field>;

    /// Returns a Pedersen commitment for the given (up to) 64-bit input and randomizer.
    fn commit_ped64(input: &[bool], randomizer: &Self::Scalar) -> Result<Self::Field>;

    /// Returns a Pedersen commitment for the given (up to) 128-bit input and randomizer.
    fn commit_ped128(input: &[bool], randomizer: &Self::Scalar) -> Result<Self::Field>;

    /// Returns the encryption domain as a constant field element.
    fn encryption_domain() -> Self::Field;

    /// Returns the MAC domain as a constant field element.
    fn mac_domain() -> Self::Field;

    /// Returns the randomizer domain as a constant field element.
    fn randomizer_domain() -> Self::Field;

    /// Returns the scalar multiplication on the group bases.
    fn g_scalar_multiply(scalar: &Self::Scalar) -> <Self::Affine as AffineCurve>::Projective;

    /// Returns the BHP hash for a given (up to) 256-bit input.
    fn hash_bhp256(input: &[bool]) -> Result<Self::Field>;

    /// Returns the BHP hash for a given (up to) 512-bit input.
    fn hash_bhp512(input: &[bool]) -> Result<Self::Field>;

    /// Returns the BHP hash for a given (up to) 768-bit input.
    fn hash_bhp768(input: &[bool]) -> Result<Self::Field>;

    /// Returns the BHP hash for a given (up to) 1024-bit input.
    fn hash_bhp1024(input: &[bool]) -> Result<Self::Field>;

    /// Returns the Pedersen hash for a given (up to) 64-bit input.
    fn hash_ped64(input: &[bool]) -> Result<Self::Field>;

    /// Returns the Pedersen hash for a given (up to) 128-bit input.
    fn hash_ped128(input: &[bool]) -> Result<Self::Field>;

    /// Returns the Poseidon hash with an input rate of 2.
    fn hash_psd2(input: &[Self::Field]) -> Result<Self::Field>;

    /// Returns the Poseidon hash with an input rate of 4.
    fn hash_psd4(input: &[Self::Field]) -> Result<Self::Field>;

    /// Returns the Poseidon hash with an input rate of 8.
    fn hash_psd8(input: &[Self::Field]) -> Result<Self::Field>;

    /// Returns the extended Poseidon hash with an input rate of 2.
    fn hash_many_psd2(input: &[Self::Field], num_outputs: usize) -> Vec<Self::Field>;

    /// Returns the extended Poseidon hash with an input rate of 4.
    fn hash_many_psd4(input: &[Self::Field], num_outputs: usize) -> Vec<Self::Field>;

    /// Returns the extended Poseidon hash with an input rate of 8.
    fn hash_many_psd8(input: &[Self::Field], num_outputs: usize) -> Vec<Self::Field>;

    /// Returns the Poseidon hash with an input rate of 2 on the scalar field.
    fn hash_to_scalar_psd2(input: &[Self::Field]) -> Result<Self::Scalar>;

    /// Returns the Poseidon hash with an input rate of 4 on the scalar field.
    fn hash_to_scalar_psd4(input: &[Self::Field]) -> Result<Self::Scalar>;

    /// Returns the Poseidon hash with an input rate of 8 on the scalar field.
    fn hash_to_scalar_psd8(input: &[Self::Field]) -> Result<Self::Scalar>;

    /// Returns the Poseidon PRF with an input rate of 2.
    fn prf_psd2(seed: &Self::Field, input: &[Self::Field]) -> Result<Self::Field>;

    /// Returns the Poseidon PRF with an input rate of 4.
    fn prf_psd4(seed: &Self::Field, input: &[Self::Field]) -> Result<Self::Field>;

    /// Returns the Poseidon PRF with an input rate of 8.
    fn prf_psd8(seed: &Self::Field, input: &[Self::Field]) -> Result<Self::Field>;
}
