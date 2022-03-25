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

use crate::{LinearCombination, Mode};
use snarkvm_fields::traits::*;

use core::{
    cmp::Ordering,
    fmt,
    ops::{Add, Sub},
};
use std::rc::Rc;

pub type Index = u64;

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Variable<F: PrimeField> {
    Constant(Rc<F>),
    Public(Index, Rc<F>),
    Private(Index, Rc<F>),
}

impl<F: PrimeField> Variable<F> {
    ///
    /// Returns `true` if the variable is a constant.
    ///
    pub fn is_constant(&self) -> bool {
        matches!(self, Self::Constant(..))
    }

    ///
    /// Returns `true` if the variable is public.
    ///
    pub fn is_public(&self) -> bool {
        matches!(self, Self::Public(..))
    }

    ///
    /// Returns `true` if the variable is private.
    ///
    pub fn is_private(&self) -> bool {
        matches!(self, Self::Private(..))
    }

    ///
    /// Returns the mode of the variable.
    ///
    pub fn mode(&self) -> Mode {
        match self {
            Self::Constant(..) => Mode::Constant,
            Self::Public(..) => Mode::Public,
            Self::Private(..) => Mode::Private,
        }
    }

    ///
    /// Returns the relative index of the variable.
    ///
    pub fn index(&self) -> Index {
        match self {
            Self::Constant(..) => 0,
            Self::Public(index, ..) => *index,
            Self::Private(index, ..) => *index,
        }
    }

    ///
    /// Returns the value of the variable.
    ///
    pub fn value(&self) -> F {
        match self {
            Self::Constant(value) => **value,
            Self::Public(_, value) => **value,
            Self::Private(_, value) => **value,
        }
    }
}

impl<F: PrimeField> PartialOrd for Variable<F> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<F: PrimeField> Ord for Variable<F> {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Self::Constant(v1), Self::Constant(v2)) => v1.cmp(v2),
            (Self::Constant(..), Self::Public(..)) => Ordering::Less,
            (Self::Constant(..), Self::Private(..)) => Ordering::Less,
            (Self::Public(..), Self::Constant(..)) => Ordering::Greater,
            (Self::Private(..), Self::Constant(..)) => Ordering::Greater,
            (Self::Public(i1, ..), Self::Public(i2, ..)) => i1.cmp(i2),
            (Self::Private(i1, ..), Self::Private(i2, ..)) => i1.cmp(i2),
            (Self::Public(..), Self::Private(..)) => Ordering::Less,
            (Self::Private(..), Self::Public(..)) => Ordering::Greater,
        }
    }
}

#[allow(clippy::op_ref)]
impl<F: PrimeField> Add<Variable<F>> for Variable<F> {
    type Output = LinearCombination<F>;

    fn add(self, other: Variable<F>) -> Self::Output {
        self + &other
    }
}

#[allow(clippy::op_ref)]
impl<F: PrimeField> Add<Variable<F>> for &Variable<F> {
    type Output = LinearCombination<F>;

    fn add(self, other: Variable<F>) -> Self::Output {
        self + &other
    }
}

#[allow(clippy::op_ref)]
impl<F: PrimeField> Add<&Variable<F>> for Variable<F> {
    type Output = LinearCombination<F>;

    fn add(self, other: &Variable<F>) -> Self::Output {
        &self + other
    }
}

impl<F: PrimeField> Add<&Variable<F>> for &Variable<F> {
    type Output = LinearCombination<F>;

    fn add(self, other: &Variable<F>) -> Self::Output {
        match (self, other) {
            (Variable::Constant(a), Variable::Constant(b)) => Variable::Constant(Rc::new(**a + **b)).into(),
            (first, second) => LinearCombination::from([first.clone(), second.clone()]),
        }
    }
}

#[allow(clippy::op_ref)]
impl<F: PrimeField> Add<LinearCombination<F>> for Variable<F> {
    type Output = LinearCombination<F>;

    fn add(self, other: LinearCombination<F>) -> Self::Output {
        self + &other
    }
}

#[allow(clippy::op_ref)]
impl<F: PrimeField> Add<LinearCombination<F>> for &Variable<F> {
    type Output = LinearCombination<F>;

    fn add(self, other: LinearCombination<F>) -> Self::Output {
        self + &other
    }
}

#[allow(clippy::op_ref)]
impl<F: PrimeField> Add<&LinearCombination<F>> for Variable<F> {
    type Output = LinearCombination<F>;

    fn add(self, other: &LinearCombination<F>) -> Self::Output {
        &self + other
    }
}

impl<F: PrimeField> Add<&LinearCombination<F>> for &Variable<F> {
    type Output = LinearCombination<F>;

    fn add(self, other: &LinearCombination<F>) -> Self::Output {
        LinearCombination::from(self) + other
    }
}

#[allow(clippy::op_ref)]
impl<F: PrimeField> Sub<Variable<F>> for Variable<F> {
    type Output = LinearCombination<F>;

    fn sub(self, other: Variable<F>) -> Self::Output {
        self - &other
    }
}

#[allow(clippy::op_ref)]
impl<F: PrimeField> Sub<Variable<F>> for &Variable<F> {
    type Output = LinearCombination<F>;

    fn sub(self, other: Variable<F>) -> Self::Output {
        self - &other
    }
}

#[allow(clippy::op_ref)]
impl<F: PrimeField> Sub<&Variable<F>> for Variable<F> {
    type Output = LinearCombination<F>;

    fn sub(self, other: &Variable<F>) -> Self::Output {
        &self - other
    }
}

impl<F: PrimeField> Sub<&Variable<F>> for &Variable<F> {
    type Output = LinearCombination<F>;

    fn sub(self, other: &Variable<F>) -> Self::Output {
        match (self, other) {
            (Variable::Constant(a), Variable::Constant(b)) => Variable::Constant(Rc::new(**a - **b)).into(),
            (first, second) => LinearCombination::from(first) - second,
        }
    }
}

#[allow(clippy::op_ref)]
impl<F: PrimeField> Sub<LinearCombination<F>> for Variable<F> {
    type Output = LinearCombination<F>;

    fn sub(self, other: LinearCombination<F>) -> Self::Output {
        self - &other
    }
}

#[allow(clippy::op_ref)]
impl<F: PrimeField> Sub<LinearCombination<F>> for &Variable<F> {
    type Output = LinearCombination<F>;

    fn sub(self, other: LinearCombination<F>) -> Self::Output {
        self - &other
    }
}

#[allow(clippy::op_ref)]
impl<F: PrimeField> Sub<&LinearCombination<F>> for Variable<F> {
    type Output = LinearCombination<F>;

    fn sub(self, other: &LinearCombination<F>) -> Self::Output {
        &self - other
    }
}

impl<F: PrimeField> Sub<&LinearCombination<F>> for &Variable<F> {
    type Output = LinearCombination<F>;

    fn sub(self, other: &LinearCombination<F>) -> Self::Output {
        LinearCombination::from(self) - other
    }
}

impl<F: PrimeField> fmt::Debug for Variable<F> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", match self {
            Self::Constant(value) => format!("Constant({})", value),
            Self::Public(index, value) => format!("Public({}, {})", index, value),
            Self::Private(index, value) => format!("Private({}, {})", index, value),
        })
    }
}

impl<F: PrimeField> fmt::Display for Variable<F> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.value())
    }
}

#[cfg(test)]
mod tests {
    use crate::*;

    #[test]
    fn test_size() {
        assert_eq!(24, std::mem::size_of::<Variable<<Circuit as Environment>::BaseField>>());
    }
}
