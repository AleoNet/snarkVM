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

use super::*;
use snarkvm_circuit::CircuitJSON;
use snarkvm_synthesizer::CallMetrics;

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
            serde_json::from_value(request["program"].take()).map_err(de::Error::custom)?,
            // Retrieve the imports.
            serde_json::from_value(request["imports"].take()).map_err(de::Error::custom)?,
            // Retrieve the function name.
            serde_json::from_value(request["function_name"].take()).map_err(de::Error::custom)?,
        ))
    }
}

pub struct InfoResponse<N: Network> {
    program_id: ProgramID<N>,
    function_name: Identifier<N>,
    metrics: CallMetrics<N>,
    json: CircuitJSON,
}

impl<N: Network> InfoResponse<N> {
    /// Initializes a new print response.
    pub const fn new(
        program_id: ProgramID<N>,
        function_name: Identifier<N>,
        metrics: CallMetrics<N>,
        json: CircuitJSON,
    ) -> Self {
        Self { program_id, function_name, metrics, json }
    }

    /// Returns the program ID.
    pub const fn program_id(&self) -> &ProgramID<N> {
        &self.program_id
    }

    /// Returns the function name.
    pub const fn function_name(&self) -> &Identifier<N> {
        &self.function_name
    }

    /// Returns the metrics associated with the function.
    pub const fn metrics(&self) -> &CallMetrics<N> {
        &self.metrics
    }

    /// Returns the JSON representation of the constraint system for function.
    pub const fn json(&self) -> &CircuitJSON {
        &self.json
    }
}

impl<N: Network> Serialize for InfoResponse<N> {
    /// Serializes the info response into string or bytes.
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut response = serializer.serialize_struct("InfoResponse", 4)?;
        response.serialize_field("program_id", &self.program_id)?;
        response.serialize_field("function_name", &self.function_name)?;
        response.serialize_field("metrics", &self.metrics)?;
        response.serialize_field("json", &self.json)?;
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
            serde_json::from_value(response["program_id"].take()).map_err(de::Error::custom)?,
            // Retrieve the function name.
            serde_json::from_value(response["function_name"].take()).map_err(de::Error::custom)?,
            // Retrieve the metrics.
            serde_json::from_value(response["metrics"].take()).map_err(de::Error::custom)?,
            // Retrieve the json.
            serde_json::from_value(response["json"].take()).map_err(de::Error::custom)?,
        ))
    }
}

impl<N: Network> Package<N> {
    /// Returns information about the programs in the package.
    pub fn info<A: crate::circuit::Aleo<Network = N, BaseField = N::Field>>(
        &self,
        endpoint: Option<String>,
    ) -> Result<Vec<(Identifier<N>, CallMetrics<N>, CircuitJSON)>> {
        // Retrieve the main program.
        let program = self.program();
        // Retrieve the program ID.
        let program_id = program.id();

        #[cfg(feature = "aleo-cli")]
        println!("⏳ Printing information about '{}'...\n", program_id.to_string().bold());

        // Construct the process.
        let process = self.get_process()?;

        // Retrieve the imported programs.
        let imported_programs = program
            .imports()
            .keys()
            .map(|program_id| process.get_program(program_id).cloned())
            .collect::<Result<Vec<_>>>()?;

        let mut results = Vec::with_capacity(program.functions().len());

        // Synthesize each proving and verifying key.
        for function_name in program.functions().keys() {
            match endpoint {
                Some(ref endpoint) => {
                    // Prepare the request.
                    let request = InfoRequest::new(program.clone(), imported_programs.clone(), *function_name);
                    // Load the proving and verifying key.
                    let response = request.send(endpoint)?;
                    // Ensure the program ID matches.
                    ensure!(
                        response.program_id() == program_id,
                        "Program ID mismatch: {} != {program_id}",
                        response.program_id()
                    );
                    // Ensure the function name matches.
                    ensure!(
                        response.function_name() == function_name,
                        "Function name mismatch: {} != {function_name}",
                        response.function_name()
                    );
                    // Insert the information into `results`.
                    results.push((*function_name, response.metrics, response.json));
                }
                None => {
                    let (metrics, json) = process.info::<A, _>(program_id, function_name, &mut rand::thread_rng())?;
                    results.push((*function_name, metrics, json));
                }
            }
        }

        #[cfg(feature = "aleo-cli")]
        println!();

        Ok(results)
    }
}

#[cfg(test)]
mod tests {
    type CurrentAleo = snarkvm_circuit::network::AleoV0;

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
