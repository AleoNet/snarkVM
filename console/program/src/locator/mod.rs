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

mod bytes;
mod parse;
mod serialize;
mod to_fields;

use crate::{Identifier, ProgramID};
use snarkvm_console_network::prelude::*;
use snarkvm_console_types::Field;

/// A locator is of the form `{program_id}/{resource}` (i.e. `howard.aleo/notify`).
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Locator<N: Network> {
    /// The program ID.
    id: ProgramID<N>,
    /// The program resource.
    resource: Identifier<N>,
}

impl<N: Network> Locator<N> {
    /// Returns the program ID.
    #[inline]
    pub const fn program_id(&self) -> &ProgramID<N> {
        &self.id
    }

    /// Returns the program name.
    #[inline]
    pub const fn name(&self) -> &Identifier<N> {
        self.id.name()
    }

    /// Returns the network-level domain (NLD).
    #[inline]
    pub const fn network(&self) -> &Identifier<N> {
        self.id.network()
    }

    /// Returns the resource name.
    #[inline]
    pub const fn resource(&self) -> &Identifier<N> {
        &self.resource
    }
}
