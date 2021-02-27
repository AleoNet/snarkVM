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

//! This library provides the non-native field gadget for the `arkworks` constraint-writing platform.
//! The non-native field gadget can be used as a standard `FieldVar`, given
//! reasonable non-native gadget parameters.
//!
//! This file contains the implementation of three structs:
//!
//! - `NonNativeFieldParams` specifies the constraint prime field (called `BaseField`),
//!     the simulated prime field (called `TargetField`), and internal parameters
//!     searched by the Python script (see `README.md`).
//! - `NonNativeFieldVar` implements the `FieldVar` for simulating `TargetField`
//!     arithmetic within `BaseField`.
//! - `NonNativeFieldMulResultVar` is an intermediate representations of the
//!     result of multiplication, which is hidden from the `FieldVar` interface
//!     and is left for advanced users who want better performance.
//!
//! The Python script mentioned above can be found in the subdirectory `scripts`.

#![cfg_attr(not(feature = "std"), no_std)]
#![deny(
    warnings,
    unused,
    future_incompatible,
    nonstandard_style,
    rust_2018_idioms,
    missing_docs
)]
#![allow(
    clippy::redundant_closure_call,
    clippy::enum_glob_use,
    clippy::missing_errors_doc,
    clippy::cast_possible_truncation,
    clippy::unseparated_literal_suffix
)]
#![forbid(unsafe_code)]

// #[macro_use]
// extern crate ark_r1cs_std;

use std::fmt::Debug;

/// example parameters of non-native field gadget
///
/// Sample parameters for non-native field gadgets
/// - `BaseField`:              the constraint field
/// - `TargetField`:            the field being simulated
/// - `num_limbs`:              how many limbs are used
/// - `bits_per_limb`:          the size of the limbs
///
pub mod params;
/// a submodule for reducing the representations
#[doc(hidden)]
pub mod reduce;

/// a macro for computing ceil(log2(x)) for a field element x
#[doc(hidden)]
#[macro_export]
macro_rules! overhead {
    ($x:expr) => {{
        use snarkvm_utilities::biginteger::BigInteger;
        let num = $x;
        let num_bits = num.into_repr().to_bits();
        let mut skipped_bits = 0;
        for b in num_bits.iter() {
            if *b == false {
                skipped_bits += 1;
            } else {
                break;
            }
        }

        let mut is_power_of_2 = true;
        for b in num_bits.iter().skip(skipped_bits + 1) {
            if *b == true {
                is_power_of_2 = false;
            }
        }

        if is_power_of_2 {
            num_bits.len() - skipped_bits
        } else {
            num_bits.len() - skipped_bits + 1
        }
    }};
}

/// Parameters for a specific `NonNativeFieldVar` instantiation
#[derive(Clone, Debug)]
pub struct NonNativeFieldParams {
    /// The number of limbs (`BaseField` elements) used to represent a `TargetField` element. Highest limb first.
    pub num_limbs: usize,

    /// The number of bits of the limb
    pub bits_per_limb: usize,
}

mod allocated_nonnative_field_var;
pub use allocated_nonnative_field_var::*;

// mod nonnative_field_var;
// pub use nonnative_field_var::*;
//
// mod allocated_nonnative_field_mul_result_var;
// pub use allocated_nonnative_field_mul_result_var::*;
//
// mod nonnative_field_mul_result_var;
// pub use nonnative_field_mul_result_var::*;
