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
use snarkvm_algorithms::prf::PoseidonPRF;
use snarkvm_curves::{
    edwards_bls12::{EdwardsAffine, EdwardsParameters, Fq, Fr},
    AffineCurve,
};

use anyhow::{bail, Result};

thread_local! {
    /// The encryption domain as a constant field element.
    static ENCRYPTION_DOMAIN: <Testnet3 as Network>::Field = PrimeField::from_bytes_le_mod_order(b"AleoSymmetricEncryption0");
    /// The MAC domain as a constant field element.
    static MAC_DOMAIN: <Testnet3 as Network>::Field = PrimeField::from_bytes_le_mod_order(b"AleoSymmetricKeyCommitment0");
    /// The randomizer domain as a constant field element.
    static RANDOMIZER_DOMAIN: <Testnet3 as Network>::Field = PrimeField::from_bytes_le_mod_order(b"AleoRandomizer0");
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct Testnet3;

impl Network for Testnet3 {
    type AccountPRF = PoseidonPRF<Self::Scalar, 4>;
    type Affine = EdwardsAffine;
    type AffineParameters = EdwardsParameters;
    type Field = Fq;
    type Scalar = Fr;

    /// The maximum number of characters allowed in a string.
    const NUM_STRING_BYTES: u32 = u8::MAX as u32;

    /// A helper method to recover the y-coordinate given the x-coordinate for
    /// a twisted Edwards point, returning the affine curve point.
    fn affine_from_x_coordinate(x: Self::Field) -> Result<Self::Affine> {
        if let Some(element) = Self::Affine::from_x_coordinate(x, true) {
            if element.is_in_correct_subgroup_assuming_on_curve() {
                return Ok(element);
            }
        }

        if let Some(element) = Self::Affine::from_x_coordinate(x, false) {
            if element.is_in_correct_subgroup_assuming_on_curve() {
                return Ok(element);
            }
        }

        bail!("Failed to recover an affine group from an x-coordinate of {x}")
    }
}
