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

#![forbid(unsafe_code)]
#![warn(clippy::cast_possible_truncation)]

#[cfg(any(feature = "batch", feature = "transmission"))]
mod helpers;
#[cfg(any(feature = "batch", feature = "transmission"))]
pub use helpers::*;

#[cfg(feature = "batch")]
mod batch;
#[cfg(feature = "batch")]
pub use batch::*;

#[cfg(feature = "batch-certificate")]
mod batch_certificate;
#[cfg(feature = "batch-certificate")]
pub use batch_certificate::*;

#[cfg(feature = "transmission")]
mod transmission;
#[cfg(feature = "transmission")]
pub use transmission::*;

#[cfg(feature = "transmission-id")]
mod transmission_id;
#[cfg(feature = "transmission-id")]
pub use transmission_id::*;
