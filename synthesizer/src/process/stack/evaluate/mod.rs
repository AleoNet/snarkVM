// Copyright (C) 2019-2023 Aleo Systems Inc.
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

mod closure;
mod finalize;
mod function;
mod instruction;

use crate::{
    Closure, FinalizeOperation, Operand,
    CallStack,
    Registers,
    Stack,
};
use console::{
    account::Address,
    network::prelude::*,
    program::{Identifier, Literal, Plaintext, Response, Value},
    types::Field,
};

use aleo_std::prelude::{finish, lap, timer};
