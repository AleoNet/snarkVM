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
#![allow(clippy::too_many_arguments)]
#![warn(clippy::cast_possible_truncation)]
#![cfg_attr(test, allow(clippy::assertions_on_result_states))]

pub use snarkvm_console_types::prelude::*;

pub mod bhp;
pub use bhp::{BHP, BHP1024, BHP256, BHP512, BHP768};

mod blake2xs;
pub use blake2xs::Blake2Xs;

mod elligator2;
pub use elligator2::Elligator2;

mod keccak;
pub use keccak::*;

mod pedersen;
pub use pedersen::{Pedersen, Pedersen128, Pedersen64};

mod poseidon;
pub use poseidon::{Poseidon, Poseidon2, Poseidon4, Poseidon8};

mod waksman;
pub use waksman::ASWaksman;
