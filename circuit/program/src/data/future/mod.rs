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

mod to_bits;

use crate::{Boolean, Identifier, Plaintext, ProgramID, ToBits};

use snarkvm_circuit_network::Aleo;
use snarkvm_circuit_types::environment::{Eject, Inject, Mode};

/// A future.
#[derive(Clone)]
pub struct Future<A: Aleo> {
    /// The program ID.
    program_id: ProgramID<A>,
    /// The name of the function.
    function_name: Identifier<A>,
    /// The inputs.
    inputs: Vec<Plaintext<A>>,
}

#[cfg(console)]
impl<A: Aleo> Inject for Future<A> {
    type Primitive = console::Future<A::Network>;

    /// Initializes a plaintext future from a primitive.
    /// Note that a plaintext future is **always** in public mode.
    fn new(_: Mode, future: Self::Primitive) -> Self {
        Self {
            program_id: Inject::new(Mode::Public, future.program_id().clone()),
            function_name: Inject::new(Mode::Public, future.function_name().clone()),
            inputs: Inject::new(Mode::Public, future.inputs().to_vec()),
        }
    }
}

#[cfg(console)]
impl<A: Aleo> Eject for Future<A> {
    type Primitive = console::Future<A::Network>;

    /// Ejects the mode of the future.
    fn eject_mode(&self) -> Mode {
        // Aggregate the mode of the program ID, function name, and inputs.
        let program_id = self.program_id.eject_mode();
        let function_name = self.function_name.eject_mode();
        let inputs = self.inputs.iter().map(|input| input.eject_mode()).collect::<Vec<_>>().eject_mode();
        let mode = Mode::combine(program_id, [function_name, inputs]);
        // Check that the mode is public and return it.
        match mode.is_public() {
            true => Mode::Public,
            false => A::halt("Future::eject_mode: mode is not public"),
        }
    }

    /// Ejects the future.
    fn eject_value(&self) -> Self::Primitive {
        Self::Primitive::new(
            self.program_id.eject_value(),
            self.function_name.eject_value(),
            self.inputs.iter().map(|input| input.eject_value()).collect::<Vec<_>>(),
        )
    }
}

impl<A: Aleo> Future<A> {
    /// Returns the program ID.
    #[inline]
    pub const fn program_id(&self) -> &ProgramID<A> {
        &self.program_id
    }

    /// Returns the name of the function.
    #[inline]
    pub const fn function_name(&self) -> &Identifier<A> {
        &self.function_name
    }

    /// Returns the inputs.
    #[inline]
    pub fn inputs(&self) -> &[Plaintext<A>] {
        &self.inputs
    }
}
