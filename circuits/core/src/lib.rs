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
pub mod algorithms;

pub mod devnet;
pub use devnet::*;

pub mod traits;
pub use traits::*;

use snarkvm_circuits_types::{environment::Environment, Boolean, Field, Group, Scalar};

pub trait Aleo: Environment {
    /// Returns a BHP commitment for the given (up to) 256-bit input and randomness.
    fn commit_bhp256(input: &[Boolean<Self>], randomness: &Scalar<Self>) -> Field<Self>;

    /// Returns a BHP commitment for the given (up to) 512-bit input and randomness.
    fn commit_bhp512(input: &[Boolean<Self>], randomness: &Scalar<Self>) -> Field<Self>;

    /// Returns a BHP commitment for the given (up to) 1024-bit input and randomness.
    fn commit_bhp1024(input: &[Boolean<Self>], randomness: &Scalar<Self>) -> Field<Self>;

    /// Returns a Pedersen commitment for the given (up to) 64-bit input and randomness.
    fn commit_ped64(input: &[Boolean<Self>], randomness: &Scalar<Self>) -> Field<Self>;

    /// Returns a Pedersen commitment for the given (up to) 128-bit input and randomness.
    fn commit_ped128(input: &[Boolean<Self>], randomness: &Scalar<Self>) -> Field<Self>;

    /// Returns a Pedersen commitment for the given (up to) 256-bit input and randomness.
    fn commit_ped256(input: &[Boolean<Self>], randomness: &Scalar<Self>) -> Field<Self>;

    /// Returns a Pedersen commitment for the given (up to) 512-bit input and randomness.
    fn commit_ped512(input: &[Boolean<Self>], randomness: &Scalar<Self>) -> Field<Self>;

    /// Returns a Pedersen commitment for the given (up to) 1024-bit input and randomness.
    fn commit_ped1024(input: &[Boolean<Self>], randomness: &Scalar<Self>) -> Field<Self>;

    /// Returns the scalar multiplication on the group bases.
    fn g_scalar_multiply(scalar: &Scalar<Self>) -> Group<Self>;

    /// Returns the BHP hash for a given (up to) 256-bit input.
    fn hash_bhp256(input: &[Boolean<Self>]) -> Field<Self>;

    /// Returns the BHP hash for a given (up to) 512-bit input.
    fn hash_bhp512(input: &[Boolean<Self>]) -> Field<Self>;

    /// Returns the BHP hash for a given (up to) 1024-bit input.
    fn hash_bhp1024(input: &[Boolean<Self>]) -> Field<Self>;

    /// Returns a hash on the scalar field for the given input.
    fn hash_to_scalar(input: &[Field<Self>]) -> Scalar<Self>;

    /// Returns the Pedersen hash for a given (up to) 64-bit input.
    fn hash_ped64(input: &[Boolean<Self>]) -> Field<Self>;

    /// Returns the Pedersen hash for a given (up to) 128-bit input.
    fn hash_ped128(input: &[Boolean<Self>]) -> Field<Self>;

    /// Returns the Pedersen hash for a given (up to) 256-bit input.
    fn hash_ped256(input: &[Boolean<Self>]) -> Field<Self>;

    /// Returns the Pedersen hash for a given (up to) 512-bit input.
    fn hash_ped512(input: &[Boolean<Self>]) -> Field<Self>;

    /// Returns the Pedersen hash for a given (up to) 1024-bit input.
    fn hash_ped1024(input: &[Boolean<Self>]) -> Field<Self>;

    /// Returns the Poseidon hash with an input rate of 2.
    fn hash_psd2(input: &[Field<Self>]) -> Field<Self>;

    /// Returns the Poseidon hash with an input rate of 4.
    fn hash_psd4(input: &[Field<Self>]) -> Field<Self>;

    /// Returns the Poseidon hash with an input rate of 8.
    fn hash_psd8(input: &[Field<Self>]) -> Field<Self>;

    /// Returns the Poseidon PRF with an input rate of 2.
    fn prf_psd2(seed: &Field<Self>, input: &[Field<Self>]) -> Field<Self>;

    /// Returns the Poseidon PRF with an input rate of 4.
    fn prf_psd4(seed: &Field<Self>, input: &[Field<Self>]) -> Field<Self>;

    /// Returns the Poseidon PRF with an input rate of 8.
    fn prf_psd8(seed: &Field<Self>, input: &[Field<Self>]) -> Field<Self>;
}
