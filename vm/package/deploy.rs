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

use snarkvm_compiler::Transaction;
use snarkvm_console::{
    program::{Plaintext, Record},
    types::Address,
};

use super::*;

pub struct DeployRequest<N: Network> {
    transaction: Transaction<N>,
    address: Address<N>,
    program_id: ProgramID<N>,
}

impl<N: Network> DeployRequest<N> {
    /// Sends the request to the given endpoint.
    pub fn new(transaction: Transaction<N>, address: Address<N>, program_id: ProgramID<N>) -> Self {
        Self { transaction, address, program_id }
    }

    /// Sends the request to the given endpoint.
    pub fn send(&self, endpoint: &str) -> Result<DeployResponse<N>> {
        Ok(ureq::post(endpoint).send_json(self)?.into_json()?)
    }

    /// Returns the deployment transaction.
    pub const fn transaction(&self) -> &Transaction<N> {
        &self.transaction
    }

    /// Returns the program address.
    pub const fn address(&self) -> &Address<N> {
        &self.address
    }

    /// Returns the imports.
    pub const fn program_id(&self) -> &ProgramID<N> {
        &self.program_id
    }
}

impl<N: Network> Serialize for DeployRequest<N> {
    /// Serializes the deploy request into string or bytes.
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut request = serializer.serialize_struct("DeployRequest", 3)?;
        // Serialize the deployment.
        request.serialize_field("transaction", &self.transaction)?;
        // Serialize the address.
        request.serialize_field("address", &self.address)?;
        // Serialize the program id.
        request.serialize_field("program_id", &self.program_id)?;
        request.end()
    }
}

impl<'de, N: Network> Deserialize<'de> for DeployRequest<N> {
    /// Deserializes the deploy request from a string or bytes.
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        // Parse the request from a string into a value.
        let request = serde_json::Value::deserialize(deserializer)?;
        // Recover the leaf.
        Ok(Self::new(
            // Retrieve the program.
            serde_json::from_value(request["transaction"].clone()).map_err(de::Error::custom)?,
            // Retrieve the address of the program.
            serde_json::from_value(request["address"].clone()).map_err(de::Error::custom)?,
            // Retrieve the program ID.
            serde_json::from_value(request["program_id"].clone()).map_err(de::Error::custom)?,
        ))
    }
}

pub struct DeployResponse<N: Network> {
    transaction: Transaction<N>,
}

impl<N: Network> DeployResponse<N> {
    /// Initializes a new deploy response.
    pub const fn new(transaction: Transaction<N>) -> Self {
        Self { transaction }
    }

    /// Returns the deployment transaction.
    pub const fn transaction(&self) -> &Transaction<N> {
        &self.transaction
    }
}

impl<N: Network> Serialize for DeployResponse<N> {
    /// Serializes the deploy response into string or bytes.
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut response = serializer.serialize_struct("DeployResponse", 1)?;
        response.serialize_field("transaction", &self.transaction)?;
        response.end()
    }
}

impl<'de, N: Network> Deserialize<'de> for DeployResponse<N> {
    /// Deserializes the deploy response from a string or bytes.
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        // Parse the response from a string into a value.
        let response = serde_json::Value::deserialize(deserializer)?;
        // Recover the leaf.
        Ok(Self::new(
            // Retrieve the program ID.
            serde_json::from_value(response["transaction"].clone()).map_err(de::Error::custom)?,
        ))
    }
}

impl<N: Network> Package<N> {
    pub fn deploy<A: crate::circuit::Aleo<Network = N, BaseField = N::Field>>(
        &self,
        endpoint: Option<String>,
        private_key: &PrivateKey<N>,
        credits: Record<N, Plaintext<N>>,
    ) -> Result<Transaction<N>> {
        // Retrieve the main program.
        let program = self.program();
        // Retrieve the main program ID.
        let program_id = program.id();

        // Retrieve the Aleo address of the deployment caller.
        let caller = self.manifest_file().development_address();

        #[cfg(feature = "aleo-cli")]
        println!("⏳ Deploying '{}'...\n", program_id.to_string().bold());

        // Construct the process.
        let mut process = Process::<N>::load()?;

        // Add program imports to the process.
        for (imported_program, _import) in program.imports() {
            // TODO (howardwu): Add the following checks:
            //  1) the imported program ID exists *on-chain* (for the given network)
            //  2) the AVM bytecode of the imported program matches the AVM bytecode of the program *on-chain*
            //  3) consensus performs the exact same checks (in `verify_deployment`)
            let endpoint = format!("http://localhost/testnet3/program/{}", imported_program);
            match ureq::get(&endpoint).send_json(imported_program)?.into_json::<String>() {
                Ok(p) => {
                    let program = Program::<N>::from_str(&p)?;
                    // Add the import program.
                    process.add_program(&program)?;
                }
                Err(_) => {
                    bail!("The program {} needs to be deployed before {}", imported_program, program.id());
                }
            }
        }

        // Initialize the RNG.
        let rng = &mut rand::thread_rng();
        // Compute the deployment.
        let deployment = process.deploy::<A, _>(program, rng)?;

        let (_, additional_fee) = process.execute_additional_fee::<A, _>(private_key, credits, 1, rng)?;

        let deployment_transaction = Transaction::from_deployment(deployment, additional_fee)?;

        serde_json::to_writer(std::fs::File::create("deployment_transaction.json")?, &deployment_transaction)?;

        match endpoint {
            Some(ref endpoint) => {
                // Construct the deploy request.
                let request = DeployRequest::new(deployment_transaction, *caller, *program_id);
                // Send the deploy request.
                let response = request.send(endpoint)?;
                Ok(response.transaction)
            }
            None => Ok(deployment_transaction),
        }
    }
}

// #[cfg(test)]
// mod tests {
//     use super::*;

//     type CurrentNetwork = snarkvm_console::network::Testnet3;
//     type CurrentAleo = snarkvm_circuit::network::AleoV0;

//     #[test]
//     fn test_deploy() {
//         // Samples a new package at a temporary directory.
//         let (directory, package) = crate::package::test_helpers::sample_package();

//         // Deploy the package.
//         let deployment_transaction = package.deploy::<CurrentAleo>(None).unwrap();
//         if let Transaction::Deploy(_, deployment, _) = deployment_transaction {
//             // Ensure the deployment edition matches.
//             assert_eq!(<CurrentNetwork as Network>::EDITION, deployment.edition());
//             // Ensure the deployment program ID matches.
//             assert_eq!(package.program().id(), deployment.program_id());
//             // Ensure the deployment program matches.
//             assert_eq!(package.program(), deployment.program());
//         }

//         // Proactively remove the temporary directory (to conserve space).
//         std::fs::remove_dir_all(directory).unwrap();
//     }

//     #[test]
//     fn test_deploy_with_import() {
//         // Samples a new package at a temporary directory.
//         let (directory, package) = crate::package::test_helpers::sample_package_with_import();

//         // Deploy the package.
//         let deployment_transaction = package.deploy::<CurrentAleo>(None).unwrap();
//         if let Transaction::Deploy(_, deployment, _) = deployment_transaction {
//             // Ensure the deployment edition matches.
//             assert_eq!(<CurrentNetwork as Network>::EDITION, deployment.edition());
//             // Ensure the deployment program ID matches.
//             assert_eq!(package.program().id(), deployment.program_id());
//             // Ensure the deployment program matches.
//             assert_eq!(package.program(), deployment.program());
//         }

//         // Proactively remove the temporary directory (to conserve space).
//         std::fs::remove_dir_all(directory).unwrap();
//     }
// }
