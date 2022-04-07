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

use crate::traits::{AffineCurve, PairingCurve, ProjectiveCurve};
use snarkvm_fields::{Field, PrimeField, SquareRootField, ToConstraintField};

use core::{fmt::Debug, iter};

pub trait PairingEngine: Sized + 'static + Copy + Debug + PartialEq + Eq + Sync + Send {
    /// This is the scalar field of the G1/G2 groups.
    type Fr: PrimeField + SquareRootField + Into<<Self::Fr as PrimeField>::BigInteger>;

    /// The projective representation of an element in G1.
    type G1Projective: ProjectiveCurve<BaseField = Self::Fq, ScalarField = Self::Fr, Affine = Self::G1Affine>
        + From<Self::G1Affine>;

    /// The affine representation of an element in G1.
    type G1Affine: AffineCurve<BaseField = Self::Fq, ScalarField = Self::Fr, Projective = Self::G1Projective>
        + PairingCurve<PairWith = Self::G2Affine, PairingResult = Self::Fqk>
        + From<Self::G1Projective>
        + ToConstraintField<Self::Fq>;

    /// The projective representation of an element in G2.
    type G2Projective: ProjectiveCurve<BaseField = Self::Fqe, ScalarField = Self::Fr, Affine = Self::G2Affine>
        + From<Self::G2Affine>;

    /// The affine representation of an element in G2.
    type G2Affine: AffineCurve<BaseField = Self::Fqe, ScalarField = Self::Fr, Projective = Self::G2Projective>
        + PairingCurve<PairWith = Self::G1Affine, PairingResult = Self::Fqk>
        + From<Self::G2Projective>
        + ToConstraintField<Self::Fq>;

    /// The base field that hosts G1.
    type Fq: PrimeField + SquareRootField;

    /// The extension field that hosts G2.
    type Fqe: SquareRootField;

    /// The extension field that hosts the target group of the pairing.
    type Fqk: Field;

    /// Perform a miller loop with some number of (G1, G2) pairs.
    #[must_use]
    fn miller_loop<'a, I>(i: I) -> Self::Fqk
    where
        I: Iterator<
            Item = (&'a <Self::G1Affine as PairingCurve>::Prepared, &'a <Self::G2Affine as PairingCurve>::Prepared),
        >;

    /// Perform final exponentiation of the result of a miller loop.
    #[must_use]
    fn final_exponentiation(_: &Self::Fqk) -> Option<Self::Fqk>;

    /// Computes a product of pairings.
    #[must_use]
    fn product_of_pairings<'a, I>(i: I) -> Self::Fqk
    where
        I: Iterator<
            Item = (&'a <Self::G1Affine as PairingCurve>::Prepared, &'a <Self::G2Affine as PairingCurve>::Prepared),
        >,
    {
        Self::final_exponentiation(&Self::miller_loop(i)).unwrap()
    }

    /// Performs multiple pairing operations
    #[must_use]
    fn pairing<G1, G2>(p: G1, q: G2) -> Self::Fqk
    where
        G1: Into<Self::G1Affine>,
        G2: Into<Self::G2Affine>,
    {
        Self::final_exponentiation(&Self::miller_loop(iter::once((&p.into().prepare(), &q.into().prepare())))).unwrap()
    }
}
