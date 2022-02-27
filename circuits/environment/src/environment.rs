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

use crate::*;
use snarkvm_curves::{AffineCurve, TwistedEdwardsParameters};
use snarkvm_fields::traits::*;

use core::fmt;
use nom::{
    branch::alt,
    bytes::complete::tag,
    combinator::map,
    error::VerboseError,
    IResult
};

pub type ParserResult<'a, O> = IResult<&'a str, O, VerboseError<&'a str>>;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Mode {
    Constant,
    Public,
    Private,
}

impl Mode {
    /// Returns `true` if the mode is a constant.
    pub fn is_constant(&self) -> bool {
        matches!(self, Self::Constant)
    }

    /// Returns `true` if the mode is public.
    pub fn is_public(&self) -> bool {
        matches!(self, Self::Public)
    }

    /// Returns `true` if the mode is private.
    pub fn is_private(&self) -> bool {
        matches!(self, Self::Private)
    }

    /// Parses the string for the mode.
    pub fn parse(string: &str) -> ParserResult<Self> {
        alt((
            map(tag("Constant"), |_| Self::Constant),
            map(tag("Public"), |_| Self::Public),
            map(tag("Private"), |_| Self::Private),
        ))(string)
    }
}

impl fmt::Display for Mode {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::Constant => write!(f, "Constant"),
            Self::Public => write!(f, "Public"),
            Self::Private => write!(f, "Private"),
        }
    }
}

pub trait Environment: Clone + fmt::Display {
    type Affine: AffineCurve<BaseField = Self::BaseField>;
    type AffineParameters: TwistedEdwardsParameters<BaseField = Self::BaseField>;
    type BaseField: PrimeField + Copy;
    type ScalarField: PrimeField + Copy;

    /// Returns the `zero` constant.
    fn zero() -> LinearCombination<Self::BaseField>;

    /// Returns the `one` constant.
    fn one() -> LinearCombination<Self::BaseField>;

    /// Returns a new variable of the given mode and value.
    fn new_variable(mode: Mode, value: Self::BaseField) -> Variable<Self::BaseField>;

    // /// Appends the given scope to the current environment.
    // fn push_scope(name: &str);
    //
    // /// Removes the given scope from the current environment.
    // fn pop_scope(name: &str);

    fn scoped<Fn, Output>(name: &str, logic: Fn) -> Output
    where
        Fn: FnOnce() -> Output;

    /// Adds one constraint enforcing that `(A * B) == C`.
    fn enforce<Fn, A, B, C>(constraint: Fn)
    where
        Fn: FnOnce() -> (A, B, C),
        A: Into<LinearCombination<Self::BaseField>>,
        B: Into<LinearCombination<Self::BaseField>>,
        C: Into<LinearCombination<Self::BaseField>>;

    /// Adds one constraint enforcing that the given boolean is `true`.
    fn assert<Boolean: Into<LinearCombination<Self::BaseField>>>(boolean: Boolean) {
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

    /// Returns `true` if all constraints in the environment are satisfied.
    fn is_satisfied() -> bool;

    /// Returns the number of constants in the entire environment.
    fn num_constants() -> usize;

    /// Returns the number of public variables in the entire environment.
    fn num_public() -> usize;

    /// Returns the number of private variables in the entire environment.
    fn num_private() -> usize;

    /// Returns the number of constraints in the entire environment.
    fn num_constraints() -> usize;

    /// Returns the number of gates in the entire environment.
    fn num_gates() -> usize;

    /// Returns the number of constants for the current scope.
    fn num_constants_in_scope() -> usize;

    /// Returns the number of public variables for the current scope.
    fn num_public_in_scope() -> usize;

    /// Returns the number of private variables for the current scope.
    fn num_private_in_scope() -> usize;

    /// Returns the number of constraints for the current scope.
    fn num_constraints_in_scope() -> usize;

    /// Returns the number of gates for the current scope.
    fn num_gates_in_scope() -> usize;

    fn affine_from_x_coordinate(x: Self::BaseField) -> Self::Affine;

    /// Halts the program from further synthesis, evaluation, and execution in the current environment.
    fn halt<S: Into<String>, T>(message: S) -> T {
        panic!("{}", message.into())
    }

    /// Clears and initializes an empty environment.
    fn reset();
}
