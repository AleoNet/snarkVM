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

use crate::models::*;
use snarkvm_fields::traits::*;

use std::ops::{Add, Div, Mul, Neg, Not, Sub};

pub enum Mode {
    Constant,
    Public,
    Private,
}

pub trait Environment {
    type Field: PrimeField + Copy;

    fn is_satisfied() -> bool;

    fn scope(name: &str) -> CircuitSpan<Self::Field>;

    // fn scoped<'a, EE, F>(name: &str, logic: F)
    // where
    //     EE: 'a + Environment,
    //     F: FnOnce(CircuitScope<'a, EE>) -> ();

    // fn scope<E, F>(name: &str, logic: F)
    // where
    //     E: Environment<Field = Fr>,
    //     F: FnOnce(E) -> ();

    fn zero() -> LinearCombination<Self::Field>;
    fn one() -> LinearCombination<Self::Field>;

    fn new_constant(value: Self::Field) -> Variable<Self::Field>;
    fn new_public(value: Self::Field) -> Variable<Self::Field>;
    fn new_private(value: Self::Field) -> Variable<Self::Field>;

    fn enforce<Fn, A, B, C>(constraint: Fn)
    where
        Fn: FnOnce() -> (A, B, C),
        A: Into<LinearCombination<Self::Field>>,
        B: Into<LinearCombination<Self::Field>>,
        C: Into<LinearCombination<Self::Field>>;

    fn num_constants() -> usize;
    fn num_public() -> usize;
    fn num_private() -> usize;
    fn num_constraints() -> usize;
}

pub trait BooleanTrait {}
// pub trait BooleanTrait: Sized + Clone + Not {}

/// Representation of the zero value.
pub trait Zero {
    type Boolean: BooleanTrait;
    type Output;

    /// Returns a new zero constant.
    fn zero() -> Self;

    /// Returns `true` if `self` is zero.
    fn is_zero(&self) -> Self::Output;
}

/// Representation of the one value.
pub trait One {
    type Boolean: BooleanTrait;
    type Output;

    /// Returns a new one constant.
    fn one() -> Self;

    /// Returns `true` if `self` is one.
    fn is_one(&self) -> Self::Output;
}

/// Trait for equality comparisons.
pub trait Equal<Rhs: ?Sized = Self> {
    type Boolean: BooleanTrait;
    type Output;

    /// Returns `true` if `self` and `other` are equal.
    fn eq(&self, other: &Rhs) -> Self::Output;
}
