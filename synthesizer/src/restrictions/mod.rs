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

mod helpers;
pub use helpers::*;

use console::{
    network::prelude::*,
    program::{Identifier, Literal, ProgramID},
};

use indexmap::IndexMap;

/// The argument type with a format of `(is_input, index, literal)`.
pub type Argument<N> = (bool, u16, Literal<N>);

#[derive(Debug)]
pub struct Restrictions<N: Network> {
    /// The set of program IDs that are restricted from being executed.
    /// e.g. `restricted.aleo` => `..` (all blocks)
    /// e.g. `restricted.aleo` => `10..` (from block 10 onwards)
    /// e.g. `restricted.aleo` => `..10` (up to block 10)
    /// e.g. `restricted.aleo` => `10..20` (from block 10 to block 20)
    programs: IndexMap<ProgramID<N>, BlockRange>,
    /// The set of `(program ID, function ID)` pairs that are restricted from being executed.
    /// e.g. `restricted.aleo/foo` => `..` (all blocks)
    /// e.g. `restricted.aleo/foo` => `10..` (from block 10 onwards)
    /// e.g. `restricted.aleo/foo` => `..10` (up to block 10)
    /// e.g. `restricted.aleo/foo` => `10..20` (from block 10 to block 20)
    functions: IndexMap<(ProgramID<N>, Identifier<N>), BlockRange>,
    /// The set of `(program ID, function ID, argument)` triples that are restricted from being executed.
    /// e.g. `restricted.aleo/bar _ aleo1zkpxxxxx _ _` => `..` (all blocks)
    /// e.g. `restricted.aleo/bar _ aleo1zkpxxxxx _ _` => `10..` (from block 10 onwards)
    /// e.g. `restricted.aleo/bar _ aleo1zkpxxxxx _ _` => `..10` (up to block 10)
    /// e.g. `restricted.aleo/bar _ aleo1zkpxxxxx _ _` => `10..20` (from block 10 to block 20)
    arguments: IndexMap<(ProgramID<N>, Identifier<N>, Argument<N>), BlockRange>,
}

impl<N: Network> Default for Restrictions<N> {
    /// Initializes a new `Restrictions` instance.
    fn default() -> Self {
        Self::new()
    }
}

impl<N: Network> Restrictions<N> {
    /// Initializes a new `Restrictions` instance.
    pub fn new() -> Self {
        Self { programs: IndexMap::new(), functions: IndexMap::new(), arguments: IndexMap::new() }
    }
}

impl<N: Network> Restrictions<N> {
    /// Returns the set of program IDs that are restricted from being executed.
    pub fn programs(&self) -> &IndexMap<ProgramID<N>, BlockRange> {
        &self.programs
    }

    /// Returns the set of `(program ID, function ID)` pairs that are restricted from being executed.
    pub fn functions(&self) -> &IndexMap<(ProgramID<N>, Identifier<N>), BlockRange> {
        &self.functions
    }

    /// Returns the set of `(program ID, function ID, argument)` triples that are restricted from being executed.
    pub fn arguments(&self) -> &IndexMap<(ProgramID<N>, Identifier<N>, Argument<N>), BlockRange> {
        &self.arguments
    }
}

impl<N: Network> Restrictions<N> {
    /// Returns `true` if the given program ID is restricted from being executed.
    pub fn is_program_restricted(&self, program_id: &ProgramID<N>, block_height: u32) -> bool {
        self.programs.get(program_id).map_or(false, |range| range.contains(block_height))
    }

    /// Returns `true` if the given `(program ID, function ID)` pair is restricted from being executed.
    pub fn is_function_restricted(
        &self,
        program_id: &ProgramID<N>,
        function_id: &Identifier<N>,
        block_height: u32,
    ) -> bool {
        self.functions.get(&(*program_id, *function_id)).map_or(false, |range| range.contains(block_height))
    }

    /// Returns `true` if the given `(program ID, function ID, argument)` triple is restricted from being executed.
    pub fn is_argument_restricted(
        &self,
        program_id: &ProgramID<N>,
        function_id: &Identifier<N>,
        argument: &Argument<N>,
        block_height: u32,
    ) -> bool {
        self.arguments
            .get(&(*program_id, *function_id, argument.clone()))
            .map_or(false, |range| range.contains(block_height))
    }
}

impl<N: Network + Serialize> Serialize for Restrictions<N> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut state = serializer.serialize_struct("Restrictions", 3)?;
        state.serialize_field("programs", &self.programs)?;
        state.serialize_field("functions", &self.functions)?;
        state.serialize_field("arguments", &self.arguments)?;
        state.end()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::types::I8;

    type CurrentNetwork = console::network::MainnetV0;

    #[test]
    fn restrictions_default() {
        let restrictions = Restrictions::<CurrentNetwork>::default();
        assert!(restrictions.programs().is_empty());
        assert!(restrictions.functions().is_empty());
        assert!(restrictions.arguments().is_empty());
    }

    #[test]
    fn restrictions_program_restricted() {
        let mut restrictions = Restrictions::<CurrentNetwork>::default();
        let program_id = ProgramID::from_str("restricted.aleo").unwrap();
        let range = BlockRange::Range(10..20);
        restrictions.programs.insert(program_id, range);
        assert!(!restrictions.is_program_restricted(&program_id, 5));
        assert!(restrictions.is_program_restricted(&program_id, 10));
        assert!(restrictions.is_program_restricted(&program_id, 15));
        assert!(!restrictions.is_program_restricted(&program_id, 20));
        assert!(!restrictions.is_program_restricted(&program_id, 25));
    }

    #[test]
    fn restrictions_function_restricted() {
        let mut restrictions = Restrictions::<CurrentNetwork>::default();
        let program_id = ProgramID::from_str("restricted.aleo").unwrap();
        let function_id = Identifier::from_str("foo").unwrap();
        let range = BlockRange::Range(10..20);
        restrictions.functions.insert((program_id, function_id), range);
        assert!(!restrictions.is_function_restricted(&program_id, &function_id, 5));
        assert!(restrictions.is_function_restricted(&program_id, &function_id, 10));
        assert!(restrictions.is_function_restricted(&program_id, &function_id, 15));
        assert!(!restrictions.is_function_restricted(&program_id, &function_id, 20));
        assert!(!restrictions.is_function_restricted(&program_id, &function_id, 25));
    }

    #[test]
    fn restrictions_argument_restricted() {
        let mut restrictions = Restrictions::<CurrentNetwork>::default();
        let program_id = ProgramID::from_str("restricted.aleo").unwrap();
        let function_id = Identifier::from_str("foo").unwrap();
        let argument = (true, 0, Literal::I8(I8::new(0)));
        let range = BlockRange::Range(10..20);
        restrictions.arguments.insert((program_id, function_id, argument.clone()), range.clone());
        assert!(!restrictions.is_argument_restricted(&program_id, &function_id, &argument, 5));
        assert!(restrictions.is_argument_restricted(&program_id, &function_id, &argument, 10));
        assert!(restrictions.is_argument_restricted(&program_id, &function_id, &argument, 15));
        assert!(!restrictions.is_argument_restricted(&program_id, &function_id, &argument, 20));
        assert!(!restrictions.is_argument_restricted(&program_id, &function_id, &argument, 25));

        let argument = (false, 0, Literal::I8(I8::new(0)));
        restrictions.arguments.insert((program_id, function_id, argument.clone()), range.clone());
        assert!(!restrictions.is_argument_restricted(&program_id, &function_id, &argument, 5));
        assert!(restrictions.is_argument_restricted(&program_id, &function_id, &argument, 10));
        assert!(restrictions.is_argument_restricted(&program_id, &function_id, &argument, 15));
        assert!(!restrictions.is_argument_restricted(&program_id, &function_id, &argument, 20));
        assert!(!restrictions.is_argument_restricted(&program_id, &function_id, &argument, 25));

        let argument = (true, 1, Literal::I8(I8::new(0)));
        restrictions.arguments.insert((program_id, function_id, argument.clone()), range);
        assert!(!restrictions.is_argument_restricted(&program_id, &function_id, &argument, 5));
        assert!(restrictions.is_argument_restricted(&program_id, &function_id, &argument, 10));
        assert!(restrictions.is_argument_restricted(&program_id, &function_id, &argument, 15));
        assert!(!restrictions.is_argument_restricted(&program_id, &function_id, &argument, 20));
        assert!(!restrictions.is_argument_restricted(&program_id, &function_id, &argument, 25));
    }
}
