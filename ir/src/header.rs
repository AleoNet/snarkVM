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

pub struct Header {
    pub function_offsets: Vec<u32>, // 0 is always main/entrypoint
    pub snarkvm_major: u32,
    pub snarkvm_minor: u32,
    pub snarkvm_patch: u32,
    pub main_input_types: Vec<Type>,
    pub constant_input_types: Vec<Type>,
    pub register_input_types: Vec<Type>,
    pub public_state_types: Vec<Type>,
    pub private_record_state_types: Vec<Type>,
    pub private_leaf_state_types: Vec<Type>,
}

impl Header {
    pub(crate) fn decode(header: ir::Header) -> Result<Self> {
        Ok(Self {
            function_offsets: header.function_offsets,
            snarkvm_major: header.snarkvm_major,
            snarkvm_minor: header.snarkvm_minor,
            snarkvm_patch: header.snarkvm_patch,
            main_input_types: header
                .main_input_types
                .into_iter()
                .map(Type::decode)
                .collect::<Result<Vec<Type>>>()?,
            constant_input_types: header
                .constant_input_types
                .into_iter()
                .map(Type::decode)
                .collect::<Result<Vec<Type>>>()?,
            register_input_types: header
                .register_input_types
                .into_iter()
                .map(Type::decode)
                .collect::<Result<Vec<Type>>>()?,
            public_state_types: header
                .public_state_types
                .into_iter()
                .map(Type::decode)
                .collect::<Result<Vec<Type>>>()?,
            private_record_state_types: header
                .private_record_state_types
                .into_iter()
                .map(Type::decode)
                .collect::<Result<Vec<Type>>>()?,
            private_leaf_state_types: header
                .private_leaf_state_types
                .into_iter()
                .map(Type::decode)
                .collect::<Result<Vec<Type>>>()?,
        })
    }

    pub(crate) fn encode(&self) -> ir::Header {
        ir::Header {
            function_offsets: self.function_offsets.clone(),
            snarkvm_major: self.snarkvm_major,
            snarkvm_minor: self.snarkvm_minor,
            snarkvm_patch: self.snarkvm_patch,
            main_input_types: self.main_input_types.iter().map(|x| x.encode()).collect(),
            constant_input_types: self.constant_input_types.iter().map(|x| x.encode()).collect(),
            register_input_types: self.register_input_types.iter().map(|x| x.encode()).collect(),
            public_state_types: self.public_state_types.iter().map(|x| x.encode()).collect(),
            private_record_state_types: self.private_record_state_types.iter().map(|x| x.encode()).collect(),
            private_leaf_state_types: self.private_leaf_state_types.iter().map(|x| x.encode()).collect(),
        }
    }
}
