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

mod constants;
use constants::*;

mod hash;

use crate::HashMany;
use snarkvm_circuit_types::{integers::Integer, prelude::*, Environment, Inject, IntegerType, Mode};
use std::borrow::Cow;

/// Sha hash with a 256-bit output.
pub type Sha256<E> = Sha<E, 256>;
pub type SHA512<E> = Sha<E, 512>;

#[derive(Clone)]
pub struct Sha<E: Environment, const NUM_BITS: usize> {
    phantom: std::marker::PhantomData<E>,
}

impl<E: Environment, const NUM_BITS: usize> Default for Sha<E, NUM_BITS> {
    fn default() -> Self {
        Self { phantom: std::marker::PhantomData }
    }
}
