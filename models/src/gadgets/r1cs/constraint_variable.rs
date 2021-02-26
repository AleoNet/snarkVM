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

use crate::{
    curves::Field,
    gadgets::r1cs::{ConstraintVar, ConstraintVar::*, LinearCombination, Variable},
};

use std::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub};

/// Either a `Variable` or a `LinearCombination`.
#[derive(Clone, Debug)]
pub enum ConstraintVariable<F: Field> {
    /// A wrapper around a `LinearCombination`.
    LC(LinearCombination<F>),
    /// A wrapper around a `Variable`.
    Var(Variable),
}

impl<F: Field> From<Variable> for ConstraintVariable<F> {
    #[inline]
    fn from(var: Variable) -> Self {
        Var(var)
    }
}

impl<F: Field> From<(F, Variable)> for ConstraintVariable<F> {
    #[inline]
    fn from(coeff_var: (F, Variable)) -> Self {
        LC(coeff_var.into())
    }
}

impl<F: Field> From<LinearCombination<F>> for ConstraintVariable<F> {
    #[inline]
    fn from(lc: LinearCombination<F>) -> Self {
        LC(lc)
    }
}

impl<F: Field> From<(F, LinearCombination<F>)> for ConstraintVariable<F> {
    #[inline]
    fn from((coeff, mut lc): (F, LinearCombination<F>)) -> Self {
        lc *= coeff;
        LC(lc)
    }
}

impl<F: Field> From<(F, ConstraintVariable<F>)> for ConstraintVariable<F> {
    #[inline]
    fn from((coeff, var): (F, ConstraintVariable<F>)) -> Self {
        match var {
            LC(lc) => (coeff, lc).into(),
            Var(var) => (coeff, var).into(),
        }
    }
}

impl<F: Field> ConstraintVariable<F> {
    /// Returns an empty linear combination.
    #[inline]
    pub fn zero() -> Self {
        LC(LinearCombination::zero())
    }

    /// Negate the coefficients of all variables in `self`.
    pub fn negate_in_place(&mut self) {
        match self {
            LC(ref mut lc) => lc.negate_in_place(),
            Var(var) => *self = (-F::one(), *var).into(),
        }
    }

    /// Double the coefficients of all variables in `self`.
    pub fn double_in_place(&mut self) {
        match self {
            LC(lc) => lc.double_in_place(),
            Var(var) => *self = (F::one().double(), *var).into(),
        }
    }
}

impl<F: Field> Add<LinearCombination<F>> for ConstraintVariable<F> {
    type Output = LinearCombination<F>;

    #[inline]
    fn add(self, other_lc: LinearCombination<F>) -> LinearCombination<F> {
        match self {
            LC(lc) => other_lc + lc,
            Var(var) => other_lc + var,
        }
    }
}

impl<F: Field> Sub<LinearCombination<F>> for ConstraintVariable<F> {
    type Output = LinearCombination<F>;

    #[inline]
    fn sub(self, other_lc: LinearCombination<F>) -> LinearCombination<F> {
        let result = match self {
            LC(lc) => other_lc - lc,
            Var(var) => other_lc - var,
        };
        -result
    }
}

impl<F: Field> Add<LinearCombination<F>> for &ConstraintVariable<F> {
    type Output = LinearCombination<F>;

    #[inline]
    fn add(self, other_lc: LinearCombination<F>) -> LinearCombination<F> {
        match self {
            LC(lc) => other_lc + lc,
            Var(var) => other_lc + *var,
        }
    }
}

impl<F: Field> Sub<LinearCombination<F>> for &ConstraintVariable<F> {
    type Output = LinearCombination<F>;

    #[inline]
    fn sub(self, other_lc: LinearCombination<F>) -> LinearCombination<F> {
        let result = match self {
            LC(lc) => other_lc - lc,
            Var(var) => other_lc - *var,
        };
        -result
    }
}

impl<F: Field> Add<(F, Variable)> for ConstraintVariable<F> {
    type Output = Self;

    #[inline]
    fn add(self, var: (F, Variable)) -> Self {
        let lc = match self {
            LC(lc) => lc + var,
            Var(var2) => LinearCombination::from(var2) + var,
        };
        LC(lc)
    }
}

impl<F: Field> AddAssign<(F, Variable)> for ConstraintVariable<F> {
    #[inline]
    fn add_assign(&mut self, var: (F, Variable)) {
        match self {
            LC(ref mut lc) => *lc += var,
            Var(var2) => *self = LC(LinearCombination::from(*var2) + var),
        };
    }
}

impl<F: Field> Neg for ConstraintVariable<F> {
    type Output = Self;

    #[inline]
    fn neg(mut self) -> Self {
        self.negate_in_place();
        self
    }
}

impl<F: Field> Mul<F> for ConstraintVariable<F> {
    type Output = Self;

    #[inline]
    fn mul(self, scalar: F) -> Self {
        match self {
            LC(lc) => LC(lc * scalar),
            Var(var) => (scalar, var).into(),
        }
    }
}

impl<F: Field> MulAssign<F> for ConstraintVariable<F> {
    #[inline]
    fn mul_assign(&mut self, scalar: F) {
        match self {
            LC(lc) => *lc *= scalar,
            Var(var) => *self = (scalar, *var).into(),
        }
    }
}

impl<F: Field> Sub<(F, Variable)> for ConstraintVariable<F> {
    type Output = Self;

    #[inline]
    fn sub(self, (coeff, var): (F, Variable)) -> Self {
        self + (-coeff, var)
    }
}

impl<F: Field> Add<Variable> for ConstraintVariable<F> {
    type Output = Self;

    fn add(self, other: Variable) -> Self {
        self + (F::one(), other)
    }
}

impl<F: Field> Sub<Variable> for ConstraintVariable<F> {
    type Output = Self;

    #[inline]
    fn sub(self, other: Variable) -> Self {
        self - (F::one(), other)
    }
}

impl<'a, F: Field> Add<&'a Self> for ConstraintVariable<F> {
    type Output = Self;

    #[inline]
    fn add(self, other: &'a Self) -> Self {
        let lc = match self {
            LC(lc2) => lc2,
            Var(var) => var.into(),
        };
        let lc2 = match other {
            LC(lc2) => lc + lc2,
            Var(var) => lc + *var,
        };
        LC(lc2)
    }
}

impl<'a, F: Field> Sub<&'a Self> for ConstraintVariable<F> {
    type Output = Self;

    #[inline]
    fn sub(self, other: &'a Self) -> Self {
        let lc = match self {
            LC(lc2) => lc2,
            Var(var) => var.into(),
        };
        let lc2 = match other {
            LC(lc2) => lc - lc2,
            Var(var) => lc - *var,
        };
        LC(lc2)
    }
}

impl<F: Field> Add<&ConstraintVariable<F>> for &ConstraintVariable<F> {
    type Output = ConstraintVariable<F>;

    #[inline]
    fn add(self, other: &ConstraintVariable<F>) -> Self::Output {
        (ConstraintVariable::zero() + self) + other
    }
}

impl<F: Field> Sub<&ConstraintVariable<F>> for &ConstraintVariable<F> {
    type Output = ConstraintVariable<F>;

    #[inline]
    fn sub(self, other: &ConstraintVariable<F>) -> Self::Output {
        (ConstraintVariable::zero() + self) - other
    }
}

impl<'a, F: Field> Add<(F, &'a Self)> for ConstraintVariable<F> {
    type Output = Self;

    #[inline]
    fn add(self, (coeff, other): (F, &'a Self)) -> Self {
        let mut lc = match self {
            LC(lc2) => lc2,
            Var(var) => LinearCombination::zero() + var,
        };

        lc = match other {
            LC(lc2) => lc + (coeff, lc2),
            Var(var) => lc + (coeff, *var),
        };
        LC(lc)
    }
}

impl<'a, F: Field> Sub<(F, &'a Self)> for ConstraintVariable<F> {
    type Output = Self;

    #[inline]
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn sub(self, (coeff, other): (F, &'a Self)) -> Self {
        let mut lc = match self {
            LC(lc2) => lc2,
            Var(var) => LinearCombination::zero() + var,
        };
        lc = match other {
            LC(lc2) => lc - (coeff, lc2),
            Var(var) => lc - (coeff, *var),
        };
        LC(lc)
    }
}
