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

/// Implementation of an AHP gadget.
pub mod ahp;

/// Implementations of native and constraint Lagrange interpolation.
pub mod lagrange_interpolation;

/// Methods to compute vanishing polynomial equations.
pub mod polynomial;

/// The Marlin proof gadget.
pub mod proof;

/// Verifier keys for the Marlin proof system.
pub mod verifier_key;

use crate::PolynomialCommitment;

/// Syntactic sugar for the universal SRS in this context.
pub type UniversalSRS<F, PC> = <PC as PolynomialCommitment<F>>::UniversalParams;
