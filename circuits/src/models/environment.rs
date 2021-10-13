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

use crate::{boolean::Boolean, models::*};
use snarkvm_curves::{AffineCurve, TwistedEdwardsParameters};
use snarkvm_fields::traits::*;

#[derive(Copy, Clone, Debug)]
pub enum Mode {
    Constant,
    Public,
    Private,
}

impl Mode {
    pub fn is_constant(&self) -> bool {
        match self {
            Self::Constant => true,
            _ => false,
        }
    }
}

pub trait Environment: Clone {
    type Affine: AffineCurve<BaseField = Self::BaseField>;
    type AffineParameters: TwistedEdwardsParameters<BaseField = Self::BaseField>;
    type BaseField: PrimeField + Copy;

    fn new_variable(mode: Mode, value: Self::BaseField) -> Variable<Self::BaseField>;

    fn zero() -> LinearCombination<Self::BaseField>;

    fn one() -> LinearCombination<Self::BaseField>;

    fn is_satisfied() -> bool;

    fn scope(name: &str) -> CircuitScope<Self::BaseField>;

    fn scoped<Fn>(name: &str, logic: Fn)
    where
        Fn: FnOnce(CircuitScope<Self::BaseField>);

    /// Adds one constraint enforcing that `(A * B) == C`.
    fn enforce<Fn, A, B, C>(constraint: Fn)
    where
        Fn: FnOnce() -> (A, B, C),
        A: Into<LinearCombination<Self::BaseField>>,
        B: Into<LinearCombination<Self::BaseField>>,
        C: Into<LinearCombination<Self::BaseField>>;

    /// Adds one constraint enforcing that the given boolean is `true`.
    fn assert(boolean: &Boolean<Self>) {
        Self::enforce(|| (boolean, Self::one(), Self::one()))
    }

    /// Adds one constraint enforcing that the `A == B`.
    fn assert_eq<A, B>(a: A, b: B)
    where
        A: Into<LinearCombination<Self::BaseField>>,
        B: Into<LinearCombination<Self::BaseField>>,
    {
        Self::enforce(|| (a, Self::one(), b))
    }

    fn num_constants() -> usize;
    fn num_public() -> usize;
    fn num_private() -> usize;
    fn num_constraints() -> usize;

    fn num_constants_in_scope(scope: &Scope) -> usize;
    fn num_public_in_scope(scope: &Scope) -> usize;
    fn num_private_in_scope(scope: &Scope) -> usize;
    fn num_constraints_in_scope(scope: &Scope) -> usize;

    fn affine_from_x_coordinate(x: Self::BaseField) -> Self::Affine;

    fn halt<S: Into<String>, T>(message: S) -> T {
        panic!("{}", message.into())
    }
}
