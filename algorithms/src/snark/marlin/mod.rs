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

//! A crate for the Marlin preprocessing zkSNARK for R1CS.
//!
//! # Note
//!
//! Currently, Marlin only supports R1CS instances where the number of inputs
//! is the same as the number of constraints (i.e., where the constraint
//! matrices are square). Furthermore, Marlin only supports instances where the
//! public inputs are of size one less than a power of 2 (i.e., 2^n - 1).
#![forbid(unsafe_code)]
#![allow(clippy::module_inception)]
#![allow(clippy::type_complexity)]

/// Implements an Algebraic Holographic Proof (AHP) for the R1CS indexed relation.
pub mod ahp;
pub use ahp::*;

pub(crate) mod data_structures;
pub use data_structures::*;

/// Errors.
mod errors;
pub use errors::*;

/// RNGs for the Marlin SNARK.
pub mod fiat_shamir;
pub use fiat_shamir::*;

/// Implements the base Marlin zkSNARK proof system.
mod marlin;
pub use marlin::*;

/// Specifies the Marlin mode.
mod mode;
pub use mode::*;

/// Parameters of non-native field gadget
///
/// Sample parameters for non-native field gadgets
/// - `BaseField`:              the constraint field
/// - `TargetField`:            the field being simulated
/// - `num_limbs`:              how many limbs are used
/// - `bits_per_limb`:          the size of the limbs
///
pub mod params;

#[cfg(test)]
pub mod tests;
