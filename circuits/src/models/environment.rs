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
    type Field: PrimeField + Copy;

    fn new_variable(mode: Mode, value: Self::Field) -> Variable<Self::Field>;

    fn zero() -> LinearCombination<Self::Field>;

    fn one() -> LinearCombination<Self::Field>;

    fn is_satisfied() -> bool;

    fn scope(name: &str) -> CircuitScope<Self::Field>;

    fn scoped<Fn>(name: &str, logic: Fn)
    where
        Fn: FnOnce(CircuitScope<Self::Field>) -> ();

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

    fn halt<T>(message: &'static str) -> T {
        eprintln!("{}", message);
        panic!("{}", message)
    }
}
