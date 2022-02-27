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

#![allow(non_snake_case)]

mod circuit;
pub(crate) use circuit::*;

mod circuit_info;
pub(crate) use circuit_info::*;

mod constraint_system;
pub(crate) use constraint_system::*;

mod indexer;

/// Represents a matrix.
pub(crate) type Matrix<F> = Vec<Vec<(F, usize)>>;

pub(crate) fn num_non_zero<F>(joint_matrix: &Matrix<F>) -> usize {
    joint_matrix.iter().map(|row| row.len()).sum()
}
