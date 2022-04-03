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

pub mod definition;
pub use definition::*;

pub mod function;
pub use function::*;

pub mod helpers;
pub use helpers::*;

pub mod process;
pub use process::*;

use snarkvm_circuits::{Aleo, Environment, Parser};

use core::{fmt::Debug, hash::Hash};

pub trait Program: Copy + Clone + Debug + Eq + PartialEq + Hash + Parser<Environment = Self::Aleo> {
    type Aleo: Aleo;

    /// The maximum number of bytes for an identifier.
    const NUM_IDENTIFIER_BYTES: usize = 31;
    /// The maximum number of inputs for a function.
    const NUM_INPUTS: usize = u16::MAX as usize;
    /// The maximum number of instructions for a function.
    const NUM_INSTRUCTIONS: usize = u32::MAX as usize;
    /// The maximum number of outputs for a function.
    const NUM_OUTPUTS: usize = u16::MAX as usize;

    /// Adds a new definition to the program.
    ///
    /// # Errors
    /// This method will halt if the definition was previously added.
    fn new_definition(definition: Definition<Self>);

    /// Adds a new function to the program.
    ///
    /// # Errors
    /// This method will halt if the function was previously added.
    fn new_function(function: Function<Self>);

    /// Returns `true` if the program contains a definition with the given name.
    fn contains_definition(name: &Identifier<Self>) -> bool;

    /// Returns `true` if the program contains a function with the given name.
    fn contains_function(name: &Identifier<Self>) -> bool;

    /// Returns the definition with the given name.
    fn get_definition(name: &Identifier<Self>) -> Option<Definition<Self>>;

    /// Returns the function with the given name.
    fn get_function(name: &Identifier<Self>) -> Option<Function<Self>>;

    /// Halts the program from further synthesis, evaluation, and execution in the current environment.
    fn halt<S: Into<String>, T>(message: S) -> T {
        Self::Aleo::halt(message)
    }
}
