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

#![cfg_attr(not(feature = "std"), no_std)]
//! A crate for the Marlin preprocessing zkSNARK for R1CS.
//!
//! # Note
//!
//! Currently, Marlin only supports R1CS instances where the number of inputs
//! is the same as the number of constraints (i.e., where the constraint
//! matrices are square). Furthermore, Marlin only supports instances where the
//! public inputs are of size one less than a power of 2 (i.e., 2^n - 1).
#![allow(clippy::module_inception)]
#![deny(unused_import_braces, trivial_casts, bare_trait_objects)]
#![deny(unused_qualifications, variant_size_differences, stable_features)]
#![deny(non_shorthand_field_patterns, unused_attributes)]
#![deny(renamed_and_removed_lints, unused_allocation, unused_comparisons)]
#![deny(const_err, unused_must_use, private_in_public)]
#![warn(unused)]
#![deny(unused_extern_crates, trivial_numeric_casts)]
#![forbid(unsafe_code)]

#[macro_use]
extern crate snarkvm_profiler;

#[cfg(not(feature = "std"))]
#[macro_use]
extern crate alloc;

#[rustfmt::skip]
#[cfg(not(feature = "std"))]
use alloc::{
    collections::{BTreeSet, BTreeMap},
    string::{String, ToString},
    vec::Vec,
};

#[cfg(not(feature = "std"))]
use core::marker::PhantomData;

#[cfg(not(feature = "std"))]
use snarkvm_utilities::io::{
    Read,
    Result as IoResult,
    Write,
    {self},
};

#[rustfmt::skip]
#[cfg(feature = "std")]
use std::{
    collections::{BTreeSet, BTreeMap},
    marker::PhantomData,
    string::{String, ToString},
    vec::Vec,
    io::{Read, Write, Result as IoResult, {self}},
};
use snarkvm_polycommit::PolynomialCommitment;

#[cfg(not(feature = "std"))]
macro_rules! eprintln {
    () => {};
    ($($arg: tt)*) => {};
}

/// Implements an Algebraic Holographic Proof (AHP) for the R1CS indexed relation.
pub mod ahp;
pub use ahp::*;

/// Implements the Marlin verification gadget.
pub mod constraints;

/// Implements the base Marlin zkSNARK proof system.
pub mod marlin;

/// RNGs for the Marlin SNARK.
pub mod fiat_shamir;
pub use fiat_shamir::*;
