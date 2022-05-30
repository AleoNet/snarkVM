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

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(all(test, not(feature = "std")))]
#[macro_use]
extern crate std;

#[cfg(not(feature = "std"))]
pub use alloc::*;

#[cfg(not(feature = "std"))]
pub use core::*;

#[cfg(feature = "std")]
#[doc(hidden)]
pub use std::*;

#[cfg(not(feature = "std"))]
#[allow(unused_imports)]
#[doc(hidden)]
pub use alloc::{boxed::Box, vec::Vec};

#[cfg(feature = "std")]
#[allow(unused_imports)]
#[doc(hidden)]
pub use std::{boxed::Box, vec::Vec};

#[macro_use]
extern crate thiserror;

pub mod biginteger;
pub use biginteger::*;

pub mod bititerator;
pub use bititerator::*;

#[macro_use]
pub mod bits;
pub use bits::*;

#[macro_use]
pub mod bytes;
pub use bytes::*;

pub mod error;
pub use error::*;

pub mod iterator;
pub use iterator::*;

#[macro_use]
pub mod parallel;
pub use parallel::*;

pub mod rand;
pub use self::rand::*;

pub mod serialize;
pub use serialize::*;

#[cfg(not(feature = "std"))]
pub mod io;

#[cfg(not(feature = "std"))]
pub fn error(_msg: &'static str) -> io::Error {
    io::Error
}

#[cfg(feature = "std")]
pub fn error<S: Into<String>>(msg: S) -> io::Error {
    io::Error::new(io::ErrorKind::Other, msg.into())
}

use std::sync::atomic::{AtomicBool, AtomicU64};
// A flag used for performance purposes in the process of loading SNARK parameters; it allows the
// PairingEngine::GXAffine values contained in them to be verified using the computationally-heavy
// AffineCurve::is_in_correct_subgroup_assuming_on_curve method in parallel after the deserialization
// is complete; the other instances of PairingEngine::GXAffine are verified during deserialization.
thread_local!(pub static PROCESSING_SNARK_PARAMS: AtomicBool = AtomicBool::new(false));

// A value used in tandem with the optimization strategy enabled by PROCESSING_SNARK_PARAMS; its
// purpose is to verify that all the PairingEngine::GXAffine values that had not been validated
// using the AffineCurve::is_in_correct_subgroup_assuming_on_curve method during deserialization
// were indeed accounted for afterwards; this also future-proofs the codebase against possible
// changes to the affected objects, i.e. marlin::snark::Parameters and all of its members.
thread_local!(pub static SNARK_PARAMS_AFFINE_COUNT: AtomicU64 = AtomicU64::new(0));
