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
#![deny(unused_import_braces, unused_qualifications, trivial_casts)]
#![deny(trivial_numeric_casts, private_in_public)]
#![deny(stable_features, unreachable_pub, non_shorthand_field_patterns)]
#![deny(unused_attributes, unused_imports, unused_mut, missing_docs)]
#![deny(renamed_and_removed_lints, stable_features, unused_allocation)]
#![deny(unused_comparisons, bare_trait_objects, unused_must_use, const_err)]
#![forbid(unsafe_code)]

#[macro_use]
extern crate snarkvm_profiler;

#[cfg(not(feature = "std"))]
#[macro_use]
extern crate alloc;

#[cfg(not(feature = "std"))]
use alloc::{
    collections::BTreeMap,
    string::{String, ToString},
    vec::Vec,
};

#[cfg(feature = "std")]
use std::{
    collections::BTreeMap,
    string::{String, ToString},
    vec::Vec,
};

#[cfg(not(feature = "std"))]
macro_rules! eprintln {
    () => {};
    ($($arg: tt)*) => {};
}

/// The Marlin public parameters for a given circuit.
pub mod circuit_parameters;
pub use circuit_parameters::*;

/// The Marlin circuit proving key.
pub mod circuit_proving_key;
pub use circuit_proving_key::*;

/// The Marlin circuit verifying key.
pub mod circuit_verifying_key;
pub use circuit_verifying_key::*;

/// Implements a Fiat-Shamir based Rng that allows one to incrementally update
/// the seed based on new messages in the proof transcript.
pub mod rng;
use rng::FiatShamirRng;

mod errors;
pub use errors::*;

/// Implements an Algebraic Holographic Proof (AHP) for the R1CS indexed relation.
pub mod ahp;
pub use ahp::AHPForR1CS;

/// A generic implementation of the Marlin proof system..
pub mod marlin;
pub use marlin::*;

/// The Marlin zkSNARK proof.
pub mod proof;
pub use proof::*;

pub mod snark;
pub use snark::*;

#[cfg(test)]
mod test;

use snarkvm_polycommit::PolynomialCommitment;

/// The universal public parameters for the argument system.
pub type UniversalSRS<F, PC> = <PC as PolynomialCommitment<F>>::UniversalParams;

// /// A structured reference string which will be used to derive a circuit-specific
// /// common reference string
// pub type SRS<E> = crate::UniversalSRS<<E as PairingEngine>::Fr, MultiPC<E>>;
//
// /// A circuit-specific proving key.
// pub type ProverKey<E> = crate::CircuitProvingKey<<E as PairingEngine>::Fr, MultiPC<E>>;
//
// /// A circuit-specific verification key.
// pub type VerifierKey<E> = crate::CircuitVerifyingKey<<E as PairingEngine>::Fr, MultiPC<E>>;
//
// impl<E: PairingEngine> From<Parameters<E>> for VerifierKey<E> {
//     fn from(params: Parameters<E>) -> Self {
//         params.verifier_key
//     }
// }
