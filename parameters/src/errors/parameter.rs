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

use std::fmt::Debug;

#[derive(Debug, Error)]
pub enum ParameterError {
    #[error("expected checksum of {}, found checksum of {}", _0, _1)]
    ChecksumMismatch(String, String),

    #[error("{}: {}", _0, _1)]
    Crate(&'static str, String),

    #[error("{}", _0)]
    Message(String),

    #[error("Remote fetch is disabled, enable compiler flag for feature")]
    RemoteFetchDisabled,

    #[error("Expected size of {}, found size of {}", _0, _1)]
    SizeMismatch(usize, usize),
}

#[cfg(not(feature = "wasm"))]
impl From<curl::Error> for ParameterError {
    fn from(error: curl::Error) -> Self {
        ParameterError::Crate("curl::error", format!("{:?}", error))
    }
}

#[cfg(feature = "wasm")]
impl From<reqwest::Error> for ParameterError {
    fn from(error: reqwest::Error) -> Self {
        ParameterError::Crate("request::error", format!("{:?}", error))
    }
}

impl From<std::io::Error> for ParameterError {
    fn from(error: std::io::Error) -> Self {
        ParameterError::Crate("std::io", format!("{:?}", error))
    }
}

impl From<std::path::StripPrefixError> for ParameterError {
    fn from(error: std::path::StripPrefixError) -> Self {
        ParameterError::Crate("std::path", format!("{:?}", error))
    }
}

impl From<ParameterError> for std::io::Error {
    fn from(error: ParameterError) -> Self {
        std::io::Error::new(std::io::ErrorKind::Other, format!("{:?}", error))
    }
}
