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

use crate::{ir, Type};

use anyhow::*;

#[derive(Debug, Clone)]
pub struct Input {
    pub variable: u32,
    pub name: String,
    pub type_: Type,
}

impl Input {
    pub(crate) fn decode(input: ir::Input) -> Result<Self> {
        Ok(Self {
            variable: input.variable,
            name: input.name,
            type_: Type::decode(input.r#type.ok_or_else(|| anyhow!("missing type for input"))?)?,
        })
    }

    pub(crate) fn encode(&self) -> ir::Input {
        ir::Input {
            variable: self.variable,
            name: self.name.clone(),
            r#type: Some(self.type_.encode()),
        }
    }
}
