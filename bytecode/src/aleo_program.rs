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

use crate::{Function, Identifier, Program, Template};
use snarkvm_circuits::Devnet;

use indexmap::IndexMap;
use std::cell::RefCell;

thread_local! {
    /// The templates declared for the program.
    /// This is a map from the template name to the template.
    static TEMPLATES: RefCell<IndexMap<Identifier<AleoProgram>, Template<AleoProgram >>> = Default::default();
    /// The functions declared for the program.
    /// This is a map from the function name to the function.
    static FUNCTIONS: RefCell<IndexMap<Identifier<AleoProgram>, Function<AleoProgram >>> = Default::default();
}

#[derive(Copy, Clone, Debug, Default, Eq, PartialEq, Hash)]
pub struct AleoProgram;

impl Program for AleoProgram {
    type Environment = Devnet;

    /// Adds a new template to the program.
    ///
    /// # Errors
    /// This method will halt if the template was previously added.
    #[inline]
    fn new_template(template: Template<Self>) {
        TEMPLATES.with(|templates| {
            // Add the template to the map.
            // Ensure the template was not previously added.
            let name = template.name().clone();
            if let Some(..) = templates.borrow_mut().insert(name.clone(), template) {
                Self::halt(format!("Template \'{name}\' was previously added"))
            }
        });
    }

    /// Adds a new function to the program.
    ///
    /// # Errors
    /// This method will halt if the function was previously added.
    #[inline]
    fn new_function(function: Function<Self>) {
        FUNCTIONS.with(|functions| {
            // Add the function to the map.
            // Ensure the function was not previously added.
            let name = function.name().clone();
            if let Some(..) = functions.borrow_mut().insert(name.clone(), function) {
                Self::halt(format!("Function \'{name}\' was previously added"))
            }
        });
    }

    /// Returns `true` if the program contains a template with the given name.
    fn contains_template(name: &Identifier<Self>) -> bool {
        TEMPLATES.with(|templates| templates.borrow().contains_key(name))
    }

    /// Returns the template with the given name.
    fn get_template(name: &Identifier<Self>) -> Option<Template<Self>> {
        TEMPLATES.with(|templates| templates.borrow().get(name).cloned())
    }
}
