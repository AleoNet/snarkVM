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

/// Runs an Aleo program function
#[derive(Debug, Parser)]
pub struct Run {
    /// The function name.
    function: Identifier<CurrentNetwork>,
    /// The function inputs.
    inputs: Vec<Value<CurrentNetwork>>,
}

impl Run {
    /// Compiles an Aleo program function with the specified name.
    #[allow(clippy::format_in_format_args)]
    pub fn parse(self) -> Result<String> {
        // Derive the program directory path.
        let path = std::env::current_dir()?;

        // Load the package.
        let package = Package::open(&path)?;
        // Load the private key.
        let private_key = crate::cli::helpers::dotenv_private_key()?;

        // Initialize an RNG.
        let rng = &mut rand::thread_rng();

        // Execute the request.
        let response = package.run::<Aleo, _>(&private_key, self.function, &self.inputs, rng)?;

        // Log the outputs.
        match response.outputs().len() {
            0 => (),
            1 => println!("\n➡️  Output\n"),
            _ => println!("\n➡️  Outputs\n"),
        };
        for output in response.outputs() {
            println!("{}", format!(" • {output}"));
        }
        println!();

        // Prepare the locator.
        let locator = Locator::<CurrentNetwork>::from_str(&format!("{}/{}", package.program_id(), self.function))?;
        // Prepare the path string.
        let path_string = format!("(in \"{}\")", path.display());

        Ok(format!("✅ Finished '{}' {}", locator.to_string().bold(), path_string.dimmed()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        cli::{Command, CLI},
        prelude::{Identifier, Value},
    };

    #[test]
    fn clap_snarkvm_run() {
        let arg_vec = vec!["snarkvm", "run", "hello", "1u32", "2u32"];
        let cli = CLI::parse_from(&arg_vec);

        if let Command::Run(run) = cli.command {
            assert_eq!(run.function, Identifier::try_from(arg_vec[2]).unwrap());
            assert_eq!(run.inputs, vec![Value::try_from(arg_vec[3]).unwrap(), Value::try_from(arg_vec[4]).unwrap()]);
        } else {
            panic!("Unexpected result of clap parsing!");
        }
    }
}
