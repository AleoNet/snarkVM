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
use snarkvm_fields::PrimeField;

use std::{
    collections::HashMap,
    ops::{Add, AddAssign, Mul, Neg, Sub},
};

use rayon::prelude::*;

#[derive(Clone, Debug)]
pub struct LinearCombination<F: PrimeField> {
    constant: F,
    terms: HashMap<Variable<F>, F>,
}

impl<F: PrimeField> LinearCombination<F> {
    pub fn zero() -> Self {
        Self {
            constant: F::zero(),
            terms: Default::default(),
        }
    }

    pub fn one() -> Self {
        Variable::one().into()
    }

    pub fn is_constant(&self) -> bool {
        self.terms.is_empty()
    }

    ///
    /// Returns `true` if the linear combination represents a `Boolean` type,
    /// and is well-formed.
    ///
    /// Properties:
    /// 1. Either `constant` or `terms` is utilized, however never both.
    /// 2. Every individual variable in the linear combination must always be either `0` or `1`.
    /// 3. The value of the linear combination must always be either `0` or `1`.
    ///
    pub fn is_boolean_type(&self) -> bool {
        if self.terms.is_empty() {
            // Constant case
            self.constant.is_zero() || self.constant.is_one()
        } else if self.constant.is_zero() {
            // Public and private cases

            // Enforce property 1.
            if self.terms.is_empty() {
                return false;
            }

            // Enforce property 2.
            if self
                .terms
                .iter()
                .filter(|(v, _)| !(v.value().is_zero() || v.value().is_one()))
                .count()
                > 0
            {
                return false;
            }

            // Enforce property 3.
            let value = self.to_value();
            if !(value.is_zero() || value.is_one()) {
                return false;
            }

            true
        } else {
            // Both self.constant and self.terms contain elements. This is a violation.
            false
        }
    }

    pub fn to_value(&self) -> F {
        // Note that 200_000 is derived empirically.
        // The setup cost of Rayon is only worth it after sufficient size.
        let sum: F = match self.terms.len() > 200_000 {
            true => self
                .terms
                .par_iter()
                .map(|(variable, coefficient)| variable.value() * coefficient)
                .sum(),
            false => self
                .terms
                .iter()
                .map(|(variable, coefficient)| variable.value() * coefficient)
                .sum(),
        };

        self.constant + sum
    }
}

impl<F: PrimeField> From<Variable<F>> for LinearCombination<F> {
    fn from(variable: Variable<F>) -> Self {
        Self::from(&variable)
    }
}

impl<F: PrimeField> From<&Variable<F>> for LinearCombination<F> {
    fn from(variable: &Variable<F>) -> Self {
        Self::from(&[*variable])
    }
}

impl<F: PrimeField, const N: usize> From<[Variable<F>; N]> for LinearCombination<F> {
    fn from(variables: [Variable<F>; N]) -> Self {
        Self::from(&variables[..])
    }
}

impl<F: PrimeField, const N: usize> From<&[Variable<F>; N]> for LinearCombination<F> {
    fn from(variables: &[Variable<F>; N]) -> Self {
        Self::from(&variables[..])
    }
}

impl<F: PrimeField> From<Vec<Variable<F>>> for LinearCombination<F> {
    fn from(variables: Vec<Variable<F>>) -> Self {
        Self::from(variables.as_slice())
    }
}

impl<F: PrimeField> From<&Vec<Variable<F>>> for LinearCombination<F> {
    fn from(variables: &Vec<Variable<F>>) -> Self {
        Self::from(variables.as_slice())
    }
}

impl<F: PrimeField> From<&[Variable<F>]> for LinearCombination<F> {
    fn from(variables: &[Variable<F>]) -> Self {
        let mut output = Self::zero();
        for variable in variables {
            match variable.is_constant() {
                true => output.constant += variable.value(),
                false => match output.terms.get_mut(variable) {
                    Some(coefficient) => *coefficient += F::one(),
                    None => {
                        output.terms.insert(*variable, F::one());
                    }
                },
            }
        }
        output
    }
}

impl<F: PrimeField> Neg for LinearCombination<F> {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self::Output {
        let mut output = self.clone();
        output.constant = -output.constant;
        output
            .terms
            .iter_mut()
            .for_each(|(_, coefficient)| *coefficient = -(*coefficient));
        output
    }
}

impl<F: PrimeField> Neg for &LinearCombination<F> {
    type Output = LinearCombination<F>;

    #[inline]
    fn neg(self) -> Self::Output {
        -(self.clone())
    }
}

impl<F: PrimeField> Add<Variable<F>> for LinearCombination<F> {
    type Output = Self;

    fn add(self, other: Variable<F>) -> Self::Output {
        self + &other
    }
}

impl<F: PrimeField> Add<&Variable<F>> for LinearCombination<F> {
    type Output = Self;

    fn add(self, other: &Variable<F>) -> Self::Output {
        self + Self::from(other)
    }
}

impl<F: PrimeField> Add<LinearCombination<F>> for LinearCombination<F> {
    type Output = Self;

    fn add(self, other: Self) -> Self::Output {
        self + &other
    }
}

impl<F: PrimeField> Add<&LinearCombination<F>> for LinearCombination<F> {
    type Output = Self;

    fn add(self, other: &Self) -> Self::Output {
        if self.constant.is_zero() && self.terms.is_empty() {
            other.clone()
        } else if other.constant.is_zero() && other.terms.is_empty() {
            self
        } else if self.terms.len() > other.terms.len() {
            let mut output = self;
            output += other;
            output
        } else {
            let mut output = other.clone();
            output += self;
            output
        }
    }
}

impl<F: PrimeField> Add<&LinearCombination<F>> for &LinearCombination<F> {
    type Output = LinearCombination<F>;

    fn add(self, other: &LinearCombination<F>) -> Self::Output {
        (*self).clone() + other
    }
}

impl<F: PrimeField> AddAssign<LinearCombination<F>> for LinearCombination<F> {
    fn add_assign(&mut self, other: Self) {
        *self += &other;
    }
}

impl<F: PrimeField> AddAssign<&LinearCombination<F>> for LinearCombination<F> {
    fn add_assign(&mut self, other: &Self) {
        if other.constant.is_zero() && other.terms.is_empty() {
            return;
        }

        self.constant += other.constant;

        for (variable, other_coefficient) in other.terms.iter() {
            match variable.is_constant() {
                true => self.constant += variable.value(),
                false => match self.terms.get_mut(variable) {
                    Some(coefficient) => *coefficient += *other_coefficient,
                    None => {
                        self.terms.insert(*variable, *other_coefficient);
                    }
                },
            }
        }
    }
}

impl<F: PrimeField> Sub<Variable<F>> for LinearCombination<F> {
    type Output = Self;

    fn sub(self, other: Variable<F>) -> Self::Output {
        self - &other
    }
}

impl<F: PrimeField> Sub<&Variable<F>> for LinearCombination<F> {
    type Output = Self;

    fn sub(self, other: &Variable<F>) -> Self::Output {
        self - Self::from(other)
    }
}

impl<F: PrimeField> Sub<LinearCombination<F>> for LinearCombination<F> {
    type Output = Self;

    fn sub(self, other: Self) -> Self::Output {
        self - &other
    }
}

impl<F: PrimeField> Sub<&LinearCombination<F>> for LinearCombination<F> {
    type Output = Self;

    fn sub(self, other: &Self) -> Self::Output {
        self + (-other)
    }
}

impl<F: PrimeField> Sub<&LinearCombination<F>> for &LinearCombination<F> {
    type Output = LinearCombination<F>;

    fn sub(self, other: &LinearCombination<F>) -> Self::Output {
        self.clone() - other
    }
}

impl<F: PrimeField> Mul<F> for LinearCombination<F> {
    type Output = Self;

    fn mul(self, coefficient: F) -> Self::Output {
        self * &coefficient
    }
}

impl<F: PrimeField> Mul<&F> for LinearCombination<F> {
    type Output = Self;

    fn mul(self, coefficient: &F) -> Self::Output {
        let mut output = self.clone();
        output.constant = output.constant * coefficient;
        output
            .terms
            .iter_mut()
            .for_each(|(_, current_coefficient)| *current_coefficient *= coefficient);
        output
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_fields::{One as O, Zero as Z};

    #[test]
    fn test_zero() {
        let zero = <Circuit as Environment>::Field::zero();

        let candidate = LinearCombination::zero();
        assert_eq!(zero, candidate.constant);
        assert!(candidate.terms.is_empty());
        assert_eq!(zero, candidate.to_value());
    }

    #[test]
    fn test_one() {
        let zero = <Circuit as Environment>::Field::zero();
        let one = <Circuit as Environment>::Field::one();

        let candidate = LinearCombination::one();
        assert_eq!(zero, candidate.constant);
        assert_eq!(1, candidate.terms.len());
        assert_eq!(one, candidate.to_value());

        let (candidate_variable, candidate_coefficient) = candidate.terms.iter().next().unwrap();
        assert!(candidate_variable.is_public());
        assert_eq!(one, candidate_variable.value());
        assert_eq!(one, *candidate_coefficient);
    }

    #[test]
    fn test_is_constant() {
        let zero = <Circuit as Environment>::Field::zero();
        let one = <Circuit as Environment>::Field::one();

        let candidate = LinearCombination::zero();
        assert!(candidate.is_constant());
        assert_eq!(zero, candidate.constant);
        assert_eq!(zero, candidate.to_value());

        let candidate = LinearCombination::one();
        assert!(!candidate.is_constant());
        assert_eq!(zero, candidate.constant);
        assert_eq!(one, candidate.to_value());
    }

    #[test]
    fn test_mul() {
        let zero = <Circuit as Environment>::Field::zero();
        let one = <Circuit as Environment>::Field::one();
        let two = one + one;
        let four = two + two;

        let start = LinearCombination::one();
        assert!(!start.is_constant());
        assert_eq!(one, start.to_value());

        // Compute 1 * 4.
        let candidate = start * four;
        assert_eq!(four, candidate.to_value());
        assert_eq!(zero, candidate.constant);
        assert_eq!(1, candidate.terms.len());

        let (candidate_variable, candidate_coefficient) = candidate.terms.iter().next().unwrap();
        assert!(candidate_variable.is_public());
        assert_eq!(one, candidate_variable.value());
        assert_eq!(four, *candidate_coefficient);
    }
}
