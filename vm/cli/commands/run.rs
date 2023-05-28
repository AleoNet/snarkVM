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

pub const LOCALE: &num_format::Locale = &num_format::Locale::en;

/// Executes an Aleo program function locally
#[derive(Debug, Parser)]
pub struct Run {
    /// The function name.
    function: Identifier<CurrentNetwork>,
    /// The function inputs.
    inputs: Vec<Value<CurrentNetwork>>,
    /// Uses the specified endpoint.
    #[clap(long)]
    endpoint: Option<String>,
    /// Toggles offline mode.
    #[clap(long)]
    offline: bool,
}

impl Run {
    /// Compiles an Aleo program function with the specified name.
    #[allow(clippy::format_in_format_args)]
    pub fn parse(self) -> Result<String> {
        // Derive the program directory path.
        let path = std::env::current_dir()?;

        // Load the package.
        let package = Package::open(&path)?;

        // Initialize an RNG.
        let rng = &mut rand::thread_rng();

        // Execute the request.
        let (response, _transition, _inclusion, metrics) = package.run::<Aleo, _>(
            self.endpoint,
            package.manifest_file().development_private_key(),
            self.function,
            &self.inputs,
            rng,
        )?;

        // Count the number of times a function is called.
        let mut program_frequency = HashMap::<String, usize>::new();
        for metric in metrics.iter() {
            // Prepare the function name string.
            let function_name_string = format!("'{}/{}'", metric.program_id, metric.function_name).bold();

            // Prepare the function constraints string
            let function_constraints_string = format!(
                "{function_name_string} - {} constraints",
                metric.num_function_constraints.to_formatted_string(LOCALE)
            );

            // Increment the counter for the function call.
            match program_frequency.get_mut(&function_constraints_string) {
                Some(counter) => *counter += 1,
                None => {
                    let _ = program_frequency.insert(function_constraints_string, 1);
                }
            }
        }

        // Log the metrics.
        use num_format::ToFormattedString;

        println!("\n⛓  Constraints\n");
        for (function_constraints, counter) in program_frequency {
            // Log the constraints
            let counter_string = match counter {
                1 => "(called 1 time)".to_string().dimmed(),
                counter => format!("(called {counter} times)").dimmed(),
            };

            println!(" •  {function_constraints} {counter_string}",)
        }

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

        Ok(format!("✅ Executed '{}' {}", locator.to_string().bold(), path_string.dimmed()))
    }
}
