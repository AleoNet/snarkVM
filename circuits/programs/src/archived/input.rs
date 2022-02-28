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

use crate::{Immediate, Memory};
use snarkvm_circuits::{Affine, BaseField, Boolean, Eject, Environment, Mode, Parser, ParserResult};

use core::fmt;
use nom::{branch::alt, combinator::map};

#[derive(Clone)]
pub struct Input<M: Memory>(Immediate<M::Environment>);

impl<M: Memory> Input<M> {
    /// Initializes a new input.
    pub fn new(input: Immediate<M::Environment>) -> Self {
        match input.is_constant() {
            true => M::halt("Attempted to assign a constant value as a function input"),
            false => {
                let register = M::new_register();
                self.inputs.push(Instruction::Store(register, input.into()));
                register
            }
        }
    }

    /// Returns the mode of the input.
    pub fn mode(&self) -> Mode {
        self.0.mode()
    }

    /// Returns `true` if the input is public.
    pub fn is_public(&self) -> bool {
        self.mode().is_public()
    }

    /// Returns `true` if the input is private.
    pub fn is_private(&self) -> bool {
        self.mode().is_private()
    }
}

impl<M: Memory> Parser for Input<E> {
    type Environment = E;
    type Output = Input<E>;

    /// Parses a string into an immediate.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self::Output> {
        let (string, immediate) = Immediate::parse(string)?;

    }
}

impl<M: Memory> fmt::Display for Input<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::BaseField(base) => base.fmt(f),
            Self::Boolean(boolean) => boolean.fmt(f),
            Self::Group(group) => group.fmt(f),
        }
    }
}
