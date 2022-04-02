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

#![forbid(unsafe_code)]

#[macro_use]
extern crate enum_index_derive;

pub mod aleo_program;
pub use aleo_program::*;

pub mod function;
pub use function::*;

pub mod helpers;
pub use helpers::*;

pub mod template;
pub use template::*;

use crate::Identifier;

// pub trait Program: Aleo {
pub trait Program: snarkvm_circuits::environment::Environment {
    /// The maximum number of characters in human-readable identifiers (such as function name).
    const NUM_CHARACTERS: usize = u8::MAX as usize;
    /// The maximum number of inputs for a function.
    const NUM_INPUTS: usize = u16::MAX as usize;
    /// The maximum number of instructions for a function.
    const NUM_INSTRUCTIONS: usize = u32::MAX as usize;
    /// The maximum number of outputs for a function.
    const NUM_OUTPUTS: usize = u16::MAX as usize;

    /// Adds a new template for the program.
    ///
    /// # Errors
    /// This method will halt if the template was previously added.
    fn new_template(template: Template<Self>);

    /// Adds a new function to the program.
    ///
    /// # Errors
    /// This method will halt if the function was previously added.
    fn new_function(function: Function<Self>);

    /// Returns `true` if the program contains a template with the given name.
    fn contains_template(name: &Identifier<Self>) -> bool;

    /// Returns the template with the given name.
    fn get_template(name: &Identifier<Self>) -> Option<Template<Self>>;
}
