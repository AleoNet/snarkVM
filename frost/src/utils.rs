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

use anyhow::{anyhow, Result};

use snarkvm_curves::AffineCurve;
use snarkvm_fields::{Field, One, PrimeField, Zero};

use std::ops::{Mul, Sub};

/// Calculate the Lagrange coefficient for a given participant index.
pub fn calculate_lagrange_coefficients<G: AffineCurve>(
    participant_index: u64,
    all_participant_indices: &[u64],
) -> Result<<G as AffineCurve>::ScalarField> {
    let mut numerator = <G as AffineCurve>::ScalarField::one();
    let mut denominator = <G as AffineCurve>::ScalarField::one();

    let participant_index_scalar = match <G as AffineCurve>::ScalarField::from_repr(participant_index.into()) {
        Some(scalar) => scalar,
        None => Err(anyhow!("Failed to convert participant index to scalar"))?,
    };

    for index in all_participant_indices {
        // Skip the index if it is the same as the participant index.
        if index == &participant_index {
            continue;
        }

        let scalar = match <G as AffineCurve>::ScalarField::from_repr((*index).into()) {
            Some(res) => res,
            None => return Err(anyhow!("Failed to convert index to scalar")),
        };

        numerator = numerator.mul(scalar);
        denominator = denominator.mul(scalar.sub(participant_index_scalar));
    }

    if denominator == <G as AffineCurve>::ScalarField::zero() {
        return Err(anyhow!("There was a duplicate index"));
    }

    let inverted_denominator = match denominator.inverse() {
        Some(res) => res,
        None => return Err(anyhow!("Failed to invert denominator")),
    };

    Ok(numerator.mul(inverted_denominator))
}
