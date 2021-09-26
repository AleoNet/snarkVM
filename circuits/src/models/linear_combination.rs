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

use crate::{models::*, traits::*};
use snarkvm_fields::traits::*;

pub type Index = u64;

use std::ops::{Add, AddAssign, Neg, Sub};

use std::collections::{HashMap, HashSet};

use rayon::prelude::*;

#[derive(Clone, Debug)]
pub struct LinearCombination<F: PrimeField>(HashMap<Variable<F>, F>);

impl<F: PrimeField> LinearCombination<F> {
    pub fn zero() -> Self {
        Self(Default::default())
    }

    pub fn to_value(&self) -> F {
        // Note that 200_000 is derived empirically.
        // The setup cost of Rayon is only worth it after sufficient size.
        match self.0.len() > 200_000 {
            true => self
                .0
                .par_iter()
                .map(|(variable, coefficient)| variable.value() * coefficient)
                .sum(),
            false => self
                .0
                .iter()
                .map(|(variable, coefficient)| variable.value() * coefficient)
                .sum(),
        }
    }
}

impl<F: PrimeField> From<Variable<F>> for LinearCombination<F> {
    fn from(variable: Variable<F>) -> Self {
        Self::from(&variable)
    }
}

impl<F: PrimeField> From<&Variable<F>> for LinearCombination<F> {
    fn from(variable: &Variable<F>) -> Self {
        Self([(*variable, F::one())].iter().cloned().collect())
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
        let mut combination = HashMap::with_capacity(variables.len());
        for variable in variables {
            match combination.get_mut(variable) {
                Some(coefficient) => *coefficient += F::one(),
                None => {
                    combination.insert(*variable, F::one());
                }
            }
        }
        Self(combination)
    }
}

impl<F: PrimeField> Neg for LinearCombination<F> {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self::Output {
        let mut output = self.clone();
        output
            .0
            .iter_mut()
            .for_each(|(_, coefficient)| *coefficient = -(*coefficient));
        output
    }
}

impl<F: PrimeField> Neg for &LinearCombination<F> {
    type Output = LinearCombination<F>;

    #[inline]
    fn neg(self) -> Self::Output {
        let mut output = self.clone();
        output
            .0
            .iter_mut()
            .for_each(|(_, coefficient)| *coefficient = -(*coefficient));
        output
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
        if self.0.is_empty() {
            other.clone()
        } else if other.0.is_empty() {
            self
        } else if self.0.len() > other.0.len() {
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

impl<F: PrimeField> AddAssign<LinearCombination<F>> for LinearCombination<F> {
    fn add_assign(&mut self, other: Self) {
        *self += &other;
    }
}

impl<F: PrimeField> AddAssign<&LinearCombination<F>> for LinearCombination<F> {
    fn add_assign(&mut self, other: &Self) {
        if other.0.is_empty() {
            return;
        }

        for (variable, other_coefficient) in other.0.iter() {
            match self.0.get_mut(variable) {
                Some(coefficient) => *coefficient += *other_coefficient,
                None => {
                    self.0.insert(*variable, *other_coefficient);
                }
            }
        }
    }
}

impl<F: PrimeField> Sub<LinearCombination<F>> for LinearCombination<F> {
    type Output = Self;

    fn sub(self, other: Self) -> Self::Output {
        self + (-other)
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
