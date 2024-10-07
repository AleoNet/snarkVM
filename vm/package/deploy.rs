// Copyright 2024 Aleo Network Foundation
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

use crate::ledger::block::Deployment;
use snarkvm_console::prelude::DeserializeExt;

use super::*;

pub struct DeployRequest<N: Network> {
    deployment: Deployment<N>,
    program_id: ProgramID<N>,
}

impl<N: Network> DeployRequest<N> {
    /// Sends the request to the given endpoint.
    pub fn new(deployment: Deployment<N>, program_id: ProgramID<N>) -> Self {
        Self { deployment, program_id }
    }

    /// Sends the request to the given endpoint.
    pub fn send(&self, endpoint: &str) -> Result<DeployResponse<N>> {
        Ok(ureq::post(endpoint).send_json(self)?.into_json()?)
    }

    /// Returns the program.
    pub const fn deployment(&self) -> &Deployment<N> {
        &self.deployment
    }

    /// Returns the imports.
    pub const fn program_id(&self) -> &ProgramID<N> {
        &self.program_id
    }
}

impl<N: Network> Serialize for DeployRequest<N> {
    /// Serializes the deploy request into string or bytes.
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut request = serializer.serialize_struct("DeployRequest", 2)?;
        // Serialize the deployment.
        request.serialize_field("deployment", &self.deployment)?;
        // Serialize the program ID.
        request.serialize_field("program_id", &self.program_id)?;
        request.end()
    }
}

impl<'de, N: Network> Deserialize<'de> for DeployRequest<N> {
    /// Deserializes the deploy request from a string or bytes.
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        // Parse the request from a string into a value.
        let mut request = serde_json::Value::deserialize(deserializer)?;
        // Recover the leaf.
        Ok(Self::new(
            // Retrieve the program.
            DeserializeExt::take_from_value::<D>(&mut request, "deployment")?,
            // Retrieve the program ID.
            DeserializeExt::take_from_value::<D>(&mut request, "program_id")?,
        ))
    }
}

pub struct DeployResponse<N: Network> {
    deployment: Deployment<N>,
}

impl<N: Network> DeployResponse<N> {
    /// Initializes a new deploy response.
    pub const fn new(deployment: Deployment<N>) -> Self {
        Self { deployment }
    }

    /// Returns the program ID.
    pub const fn deployment(&self) -> &Deployment<N> {
        &self.deployment
    }
}

impl<N: Network> Serialize for DeployResponse<N> {
    /// Serializes the deploy response into string or bytes.
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut response = serializer.serialize_struct("DeployResponse", 1)?;
        response.serialize_field("deployment", &self.deployment)?;
        response.end()
    }
}

impl<'de, N: Network> Deserialize<'de> for DeployResponse<N> {
    /// Deserializes the deploy response from a string or bytes.
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        // Parse the response from a string into a value.
        let mut response = serde_json::Value::deserialize(deserializer)?;
        // Recover the leaf.
        Ok(Self::new(
            // Retrieve the program ID.
            DeserializeExt::take_from_value::<D>(&mut response, "deployment")?,
        ))
    }
}

impl<N: Network> Package<N> {
    pub fn deploy<A: crate::circuit::Aleo<Network = N, BaseField = N::Field>>(
        &self,
        endpoint: Option<String>,
    ) -> Result<Deployment<N>> {
        // Retrieve the main program.
        let program = self.program();
        // Retrieve the main program ID.
        let program_id = program.id();

        #[cfg(feature = "aleo-cli")]
        println!("⏳ Deploying '{}'...\n", program_id.to_string().bold());

        // Construct the process.
        let mut process = Process::<N>::load_no_storage()?;

        // Add program imports to the process.
        let imports_directory = self.imports_directory();
        program.imports().keys().try_for_each(|program_id| {
            // TODO (howardwu): Add the following checks:
            //  1) the imported program ID exists *on-chain* (for the given network)
            //  2) the AVM bytecode of the imported program matches the AVM bytecode of the program *on-chain*
            //  3) consensus performs the exact same checks (in `verify_deployment`)

            // Open the Aleo program file.
            let import_program_file = AleoFile::open(&imports_directory, program_id, false)?;
            // Add the import program.
            process.add_program(import_program_file.program())?;
            Ok::<_, Error>(())
        })?;

        // Initialize the RNG.
        let rng = &mut rand::thread_rng();
        // Compute the deployment.
        let deployment = process.deploy::<A, _>(program, rng).unwrap();

        match endpoint {
            Some(ref endpoint) => {
                // Construct the deploy request.
                let request = DeployRequest::new(deployment, *program_id);
                // Send the deploy request.
                let response = request.send(endpoint)?;
                // Ensure the program ID matches.
                ensure!(
                    response.deployment.program_id() == program_id,
                    "Program ID mismatch: {} != {program_id}",
                    response.deployment.program_id()
                );
                Ok(response.deployment)
            }
            None => Ok(deployment),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    type CurrentNetwork = snarkvm_console::network::MainnetV0;
    type CurrentAleo = snarkvm_circuit::network::AleoV0;

    #[test]
    fn test_deploy() {
        // Samples a new package at a temporary directory.
        let (directory, package) = crate::package::test_helpers::sample_token_package();

        // Deploy the package.
        let deployment = package.deploy::<CurrentAleo>(None).unwrap();

        // Ensure the deployment edition matches.
        assert_eq!(<CurrentNetwork as Network>::EDITION, deployment.edition());
        // Ensure the deployment program ID matches.
        assert_eq!(package.program().id(), deployment.program_id());
        // Ensure the deployment program matches.
        assert_eq!(package.program(), deployment.program());

        // Proactively remove the temporary directory (to conserve space).
        std::fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn test_deploy_with_import() {
        // Samples a new package at a temporary directory.
        let (directory, package) = crate::package::test_helpers::sample_wallet_package();

        // Deploy the package.
        let deployment = package.deploy::<CurrentAleo>(None).unwrap();

        // Ensure the deployment edition matches.
        assert_eq!(<CurrentNetwork as Network>::EDITION, deployment.edition());
        // Ensure the deployment program ID matches.
        assert_eq!(package.program().id(), deployment.program_id());
        // Ensure the deployment program matches.
        assert_eq!(package.program(), deployment.program());

        // Proactively remove the temporary directory (to conserve space).
        std::fs::remove_dir_all(directory).unwrap();
    }
}
