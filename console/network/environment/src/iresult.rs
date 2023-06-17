// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

pub type IResult<T> = Result<T, HaltError>;

#[derive(Debug, Error)]
pub enum HaltError {
    #[error("{}", _0)]
    Anyhow(#[from] anyhow::Error),
    #[error("{}", _0)]
    Halt(String),
}

/// Construct a halting error that can be returned early.
#[macro_export]
macro_rules! haltable {
    ($fmt:expr) => {
        $crate::HaltError::Halt(std::fmt::format(core::format_args!($fmt)))
    };
    ($fmt:expr, $($arg:tt)*) => {
        $crate::HaltError::Halt(std::fmt::format(core::format_args!($fmt, $($arg)*)))
    };
}

/// Return early with a halting error.
///
/// This macro is equivalent to `return Err(`[`haltable!($args...)`][haltable!]`)`.
///
/// The surrounding function's or closure's return value is required to be
/// `Result<_,`[`console::HaltError`][console::HaltError]`>`.
///
/// [error!]: crate::HaltError
#[macro_export]
macro_rules! halt {
    ($fmt:expr) => {
        return Err($crate::haltable!($fmt))
    };
    ($fmt:expr, $($arg:tt)*) => {
        return Err($crate::haltable!($fmt, $($arg)*))
    };
}
