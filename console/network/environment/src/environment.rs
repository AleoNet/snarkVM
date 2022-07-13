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

use crate::prelude::{Deserialize, DeserializeOwned, Serialize};
use snarkvm_curves::{
    bls12_377::Bls12_377,
    edwards_bls12::{EdwardsAffine, EdwardsParameters},
    AffineCurve,
    MontgomeryParameters,
    PairingEngine,
    ProjectiveCurve,
    TwistedEdwardsParameters,
};
use snarkvm_fields::{PrimeField, SquareRootField};
use snarkvm_utilities::BigInteger;

use core::{fmt::Debug, hash::Hash};

pub trait Environment:
    'static + Copy + Clone + Debug + PartialEq + Eq + Hash + Serialize + DeserializeOwned + Send + Sync
{
    type Affine: AffineCurve<
        Projective = Self::Projective,
        BaseField = Self::Field,
        ScalarField = Self::Scalar,
        Coordinates = (Self::Field, Self::Field),
    >;
    type AffineParameters: MontgomeryParameters<BaseField = Self::Field>
        + TwistedEdwardsParameters<BaseField = Self::Field>;
    type BigInteger: BigInteger;
    type Field: PrimeField<BigInteger = Self::BigInteger> + SquareRootField + Copy;
    type PairingCurve: PairingEngine<Fr = Self::Field>;
    type Projective: ProjectiveCurve<Affine = Self::Affine, BaseField = Self::Field, ScalarField = Self::Scalar>;
    type Scalar: PrimeField<BigInteger = Self::BigInteger> + Copy;

    /// The maximum number of bytes allowed in a string.
    const MAX_STRING_BYTES: u32 = u8::MAX as u32;

    /// Halts the program from further synthesis, evaluation, and execution in the current environment.
    fn halt<S: Into<String>, T>(message: S) -> T {
        panic!("{}", message.into())
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Console;

impl Environment for Console {
    type Affine = EdwardsAffine;
    type AffineParameters = EdwardsParameters;
    type BigInteger = <Self::Field as PrimeField>::BigInteger;
    type Field = <Self::Affine as AffineCurve>::BaseField;
    type PairingCurve = Bls12_377;
    type Projective = <Self::Affine as AffineCurve>::Projective;
    type Scalar = <Self::Affine as AffineCurve>::ScalarField;
}
