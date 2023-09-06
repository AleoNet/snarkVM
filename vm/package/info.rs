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

use super::*;

use snarkvm_utilities::DeserializeExt;

pub struct InfoRequest<N: Network> {
    program: Program<N>,
    imports: Vec<Program<N>>,
    function_name: Identifier<N>,
}

impl<N: Network> InfoRequest<N> {
    /// Initializes a new info request.
    pub const fn new(program: Program<N>, imports: Vec<Program<N>>, function_name: Identifier<N>) -> Self {
        Self { program, imports, function_name }
    }

    /// Sends the request to the given endpoint.
    pub fn send(&self, endpoint: &str) -> Result<InfoResponse<N>> {
        Ok(ureq::get(endpoint).send_json(self)?.into_json()?)
    }

    /// Returns the program.
    pub const fn program(&self) -> &Program<N> {
        &self.program
    }

    /// Returns the imports.
    pub const fn imports(&self) -> &Vec<Program<N>> {
        &self.imports
    }

    /// Returns the function name.
    pub const fn function_name(&self) -> &Identifier<N> {
        &self.function_name
    }
}

impl<N: Network> Serialize for InfoRequest<N> {
    /// Serializes the print request into string or bytes.
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut request = serializer.serialize_struct("InfoRequest", 3)?;
        request.serialize_field("program", &self.program)?;
        request.serialize_field("imports", &self.imports)?;
        request.serialize_field("function_name", &self.function_name)?;
        request.end()
    }
}

impl<'de, N: Network> Deserialize<'de> for InfoRequest<N> {
    /// Deserializes the print request from a string or bytes.
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        // Parse the request from a string into a value.
        let mut request = serde_json::Value::deserialize(deserializer)?;
        // Recover the leaf.
        Ok(Self::new(
            // Retrieve the program.
            DeserializeExt::take_from_value::<D>(&mut request, "program")?,
            // Retrieve the imports.
            DeserializeExt::take_from_value::<D>(&mut request, "imports")?,
            // Retrieve the function name.
            DeserializeExt::take_from_value::<D>(&mut request, "function_name")?,
        ))
    }
}

pub struct InfoResponse<N: Network> {
    program_id: ProgramID<N>,
    function_name: Identifier<N>,
}

impl<N: Network> InfoResponse<N> {
    /// Initializes a new print response.
    pub const fn new(program_id: ProgramID<N>, function_name: Identifier<N>) -> Self {
        Self { program_id, function_name }
    }

    /// Returns the program ID.
    pub const fn program_id(&self) -> &ProgramID<N> {
        &self.program_id
    }

    /// Returns the function name.
    pub const fn function_name(&self) -> &Identifier<N> {
        &self.function_name
    }
}

impl<N: Network> Serialize for InfoResponse<N> {
    /// Serializes the info response into string or bytes.
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut response = serializer.serialize_struct("InfoResponse", 4)?;
        response.serialize_field("program_id", &self.program_id)?;
        response.serialize_field("function_name", &self.function_name)?;
        response.end()
    }
}

impl<'de, N: Network> Deserialize<'de> for InfoResponse<N> {
    /// Deserializes the info response from a string or bytes.
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        // Parse the response from a string into a value.
        let mut response = serde_json::Value::deserialize(deserializer)?;
        // Recover the leaf.
        Ok(Self::new(
            // Retrieve the program ID.
            DeserializeExt::take_from_value::<D>(&mut response, "program_id")?,
            // Retrieve the function name.
            DeserializeExt::take_from_value::<D>(&mut response, "function_name")?,
        ))
    }
}

impl<N: Network> Package<N> {
    /// Returns information about the programs in the package.
    pub fn info<A: crate::circuit::Aleo<Network = N, BaseField = N::Field>>(
        &self,
        endpoint: Option<String>,
    ) -> Result<Vec<(Identifier<N>, A::Transcript)>> {
        // Retrieve the main program.
        let program = self.program();
        // Retrieve the program ID.
        let program_id = program.id();

        #[cfg(feature = "aleo-cli")]
        println!("⏳ Printing information about '{}'...\n", program_id.to_string().bold());

        // Construct the process.
        let process = self.get_process()?;

        // Retrieve the imported programs.
        let _imported_programs = program
            .imports()
            .keys()
            .map(|program_id| process.get_program(program_id).cloned())
            .collect::<Result<Vec<_>>>()?;

        let mut results = Vec::with_capacity(program.functions().len());

        // Synthesize each proving and verifying key.
        for function_name in program.functions().keys() {
            let transcript = process.info::<A, _>(program_id, function_name, &mut rand::thread_rng())?;
            results.push((*function_name, transcript));
        }

        #[cfg(feature = "aleo-cli")]
        println!();

        Ok(results)
    }
}

#[cfg(test)]
mod tests {
    type CurrentAleo = snarkvm_circuit::network::FormalV0;

    #[test]
    fn test_build() {
        // Samples a new package at a temporary directory.
        let (directory, package) = crate::package::test_helpers::sample_package();

        // Ensure the build directory does *not* exist.
        assert!(!package.build_directory().exists());
        // Build the package.
        package.build::<CurrentAleo>(None).unwrap();
        // Ensure the build directory exists.
        assert!(package.build_directory().exists());

        // Proactively remove the temporary directory (to conserve space).
        std::fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn test_build_with_import() {
        // Samples a new package at a temporary directory.
        let (directory, package) = crate::package::test_helpers::sample_package_with_import();

        // Ensure the build directory does *not* exist.
        assert!(!package.build_directory().exists());
        // Build the package.
        package.build::<CurrentAleo>(None).unwrap();
        // Ensure the build directory exists.
        assert!(package.build_directory().exists());

        // Proactively remove the temporary directory (to conserve space).
        std::fs::remove_dir_all(directory).unwrap();
    }
}
