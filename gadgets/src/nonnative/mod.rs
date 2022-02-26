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

//! This module provides the non-native field gadget for the `snarkVM` constraint-writing platform.
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
mod allocated_nonnative_field_var;
pub use allocated_nonnative_field_var::*;

mod allocated_nonnative_field_mul_result_var;
pub use allocated_nonnative_field_mul_result_var::*;

mod nonnative_field_var;
pub use nonnative_field_var::*;

mod nonnative_field_input_var;
pub use nonnative_field_input_var::*;

mod nonnative_field_mul_result_var;
pub use nonnative_field_mul_result_var::*;

/// a submodule for reducing the representations
#[doc(hidden)]
pub mod reduce;
