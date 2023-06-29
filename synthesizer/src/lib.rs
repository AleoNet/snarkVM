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
// #![warn(clippy::cast_possible_truncation)]
#![allow(clippy::single_element_loop)]
// TODO (howardwu): Update the return type on `execute` after stabilizing the interface.
#![allow(clippy::type_complexity)]

#[macro_use]
extern crate async_trait;
#[macro_use]
extern crate tracing;

#[cfg(feature = "coinbase")]
pub use snarkvm_synthesizer_coinbase as coinbase;
#[cfg(feature = "program")]
pub use snarkvm_synthesizer_program as program;
#[cfg(feature = "snark")]
pub use snarkvm_synthesizer_snark as snark;
#[cfg(feature = "stack")]
pub use snarkvm_synthesizer_stack as stack;

pub mod block;
pub use block::*;

pub mod process;
pub use process::*;

pub mod query;
pub use query::*;

pub mod store;
pub use store::*;

pub mod vm;
pub use vm::*;

pub mod prelude {
    #[cfg(feature = "coinbase")]
    pub use crate::coinbase::*;
    #[cfg(feature = "program")]
    pub use crate::program::*;
    #[cfg(feature = "snark")]
    pub use crate::snark::*;

    // TODO (howardwu): These will be refactored into their own modules.
    //  Config flags should be added to these after modularization so that they can be disabled.
    pub use crate::{block::*, cow_to_cloned, cow_to_copied, process::*, store::*, vm::*};
}
