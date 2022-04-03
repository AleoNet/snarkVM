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

use crate::{
    function::parsers::*,
    helpers::{Locator, Register},
    Program,
    Value,
};
use snarkvm_circuits::prelude::*;

use indexmap::IndexMap;
use std::{cell::RefCell, rc::Rc};

/// The registers contains a mapping of the registers to their corresponding values in a function.
#[derive(Clone, Debug, Default)]
pub struct Registers<P: Program> {
    /// The mapping of registers to their values.
    registers: Rc<RefCell<IndexMap<Locator, Option<Value<P>>>>>,
    /// The number of registers defined in the function.
    num_defined: Rc<RefCell<Locator>>,
    /// The number of registers assigned in the function.
    num_assigned: Rc<RefCell<Locator>>,
}

impl<P: Program> Registers<P> {
    /// Initializes a new instance of the registers.
    #[inline]
    pub fn new() -> Self {
        Self {
            registers: Rc::new(RefCell::new(IndexMap::new())),
            num_defined: Default::default(),
            num_assigned: Default::default(),
        }
    }

    /// Returns `true` if the given register is defined.
    #[inline]
    pub fn is_defined(&self, register: &Register<P>) -> bool {
        // Checks if the register is defined.
        self.registers.borrow().contains_key(register.locator())
    }

    /// Returns `true` if the given register is assigned.
    #[inline]
    pub fn is_assigned(&self, register: &Register<P>) -> bool {
        // Checks if the register is assigned.
        matches!(self.registers.borrow().get(register.locator()), Some(Some(_)))
    }

    /// Defines the given register, assuming it is not already defined.
    ///
    /// # Errors
    /// This method will halt if the register locators are not monotonically increasing.
    /// This method will halt if any registers are assigned.
    /// This method wil halt if the register is a register member.
    /// This method will halt if the register is already defined.
    #[inline]
    pub fn define(&self, register: &Register<P>) {
        // Ensure the register definitions are monotonically increasing.
        if *self.num_defined.borrow() != *register.locator() {
            P::halt(format!(
                "Expected \'{}\', found \'{register}\'",
                Register::<P>::Locator(*self.num_defined.borrow())
            ))
        }

        // Ensure no registers have been assigned.
        if *self.num_assigned.borrow() != 0 {
            P::halt("Illegal operation, cannot define a new register after assigning it")
        }

        // Ensure the register is not a register member.
        match register {
            // Define the register.
            Register::Locator(locator) => {
                // Insert the unassigned register into the registers map.
                self.registers.borrow_mut().insert(*locator, None);
                // Increment the number of defined registers.
                *self.num_defined.borrow_mut() += 1;
            }
            // Halt if the register is a register member.
            Register::Member(..) => P::halt("Illegal operation, cannot define a register member"),
        }
    }

    /// Assigns the given value to the given register, assuming the register is not already assigned.
    ///
    /// # Errors
    /// This method will halt if the given register is a register member.
    /// This method will halt if the register was previously stored.
    #[inline]
    pub fn assign<V: Into<Value<P>>>(&self, register: &Register<P>, value: V) {
        // Ensure the register assignments are monotonically increasing.
        if *self.num_assigned.borrow() != *register.locator() {
            P::halt(format!(
                "Expected \'{}\', found \'{register}\'",
                Register::<P>::Locator(*self.num_assigned.borrow())
            ))
        }

        // Store the value in the register.
        let previous = match register {
            // Store the value for a register.
            Register::Locator(locator) => self.registers.borrow_mut().insert(*locator, Some(value.into())),
            // Store the value for a register member.
            Register::Member(..) => P::halt(format!("Cannot store directly to \'{register}\'")),
        };

        // Ensure the register has not been previously stored.
        match previous {
            // Halt if the register was previously stored.
            Some(Some(..)) => P::halt(format!("Register \'{register}\' was previously assigned")),
            // Increment the number of assigned registers.
            Some(None) => *self.num_assigned.borrow_mut() += 1,
            // Halt if the register was not previously defined.
            None => P::halt(format!("Register \'{register}\' was not defined before assignment")),
        }
    }

    /// Loads the value of a given operand from the registers.
    ///
    /// # Errors
    /// This method will halt if the register locator is not found.
    /// In the case of register members, this method will halt if the member is not found.
    #[inline]
    pub fn load<O: Into<Operand<P>>>(&self, operand: O) -> Value<P> {
        // Retrieve the register.
        let register = match operand.into() {
            // If the operand is a register, load the value from the register.
            Operand::Register(register) => register,
            // If the operand is a value, return the value.
            Operand::Value(value) => return value,
        };

        // Retrieve the value from the register.
        let value = match self.registers.borrow().get(register.locator()) {
            // Return the value if it exists.
            Some(Some(value)) => (*value).clone(),
            // Halts if the value does not exist.
            Some(None) | None => P::halt(format!("Failed to locate register \'{register}\'")),
        };

        // Return the value for the given register or register member.
        match register {
            // If the register is a locator, then return the value.
            Register::Locator(..) => value,
            // If the register is a register member, then load the specific value.
            Register::Member(_, ref member_name) => match value {
                // Halts if the value is not a composite.
                Value::Literal(..) => P::halt("Cannot load a register member from a literal"),
                // Retrieve the value of the member (from the value).
                Value::Composite(definition, members) => {
                    // Retrieve the member index of the identifier (from the definition).
                    let member_index = match P::get_definition(&definition) {
                        Some(definition) => {
                            definition.members().iter().position(|member| member.name() == member_name).unwrap_or_else(
                                || P::halt(format!("Failed to locate \'{member_name}\' in \'{definition}\'")),
                            )
                        }
                        // Halts if the definition does not exist.
                        None => P::halt(format!("Failed to locate \'{definition}\'")),
                    };
                    // Return the value of the member.
                    match members.get(member_index) {
                        Some(literal) => (*literal).clone().into(),
                        // Halts if the member does not exist.
                        None => P::halt(format!("Failed to locate \'{register}\'")),
                    }
                }
            },
        }
    }

    /// Returns `true` if the registers contains any assigned registers.
    #[inline]
    pub fn is_dirty(&self) -> bool {
        // Return `true` if the number of assigned registers is greater than zero.
        *self.num_assigned.borrow() > 0
    }

    /// Clears the registers of their assignments, preserving the register definitions.
    /// This allows a function to be re-executed without having to re-define the registers.
    #[inline]
    pub fn clear_assignments(&self) {
        // Clear the assignments in each register.
        self.registers.borrow_mut().values_mut().for_each(|value| *value = None);
        // Reset the number of assigned registers.
        *self.num_assigned.borrow_mut() = 0;
    }
}
