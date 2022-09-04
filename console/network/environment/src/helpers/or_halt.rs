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

use crate::Environment;

/// A trait to unwrap a `Result` or `Halt`.
pub trait OrHalt<T> {
    /// Returns the result if it is successful, otherwise halt.
    fn or_halt<E: Environment>(self) -> T;

    /// Returns the result if it is successful, otherwise halts with the message.
    fn or_halt_with<E: Environment>(self, msg: &str) -> T;
}

impl<T, Error: core::fmt::Display> OrHalt<T> for Result<T, Error> {
    /// Returns the result if it is successful, otherwise halt.
    fn or_halt<E: Environment>(self) -> T {
        match self {
            Ok(result) => result,
            Err(error) => E::halt(error.to_string()),
        }
    }

    /// Returns the result if it is successful, otherwise halts with the message.
    fn or_halt_with<E: Environment>(self, msg: &str) -> T {
        match self {
            Ok(result) => result,
            Err(error) => E::halt(format!("{msg}: {error}")),
        }
    }
}
