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

impl<N: Network, C: ConsensusStorage<N>> VM<N, C> {
    /// Authorizes a call to the program function for the given inputs.
    #[inline]
    pub fn authorize<R: Rng + CryptoRng>(
        &self,
        private_key: &PrivateKey<N>,
        program_id: impl TryInto<ProgramID<N>>,
        function_name: impl TryInto<Identifier<N>>,
        inputs: impl IntoIterator<IntoIter = impl ExactSizeIterator<Item = impl TryInto<Value<N>>>>,
        rng: &mut R,
    ) -> Result<Authorization<N>> {
        let timer = timer!("VM::authorize");

        // Prepare the program ID.
        let program_id = program_id.try_into().map_err(|_| anyhow!("Invalid program ID"))?;
        // Prepare the function name.
        let function_name = function_name.try_into().map_err(|_| anyhow!("Invalid function name"))?;
        // Prepare the inputs.
        let inputs = inputs
            .into_iter()
            .enumerate()
            .map(|(index, input)| {
                input
                    .try_into()
                    .map_err(|_| anyhow!("Failed to parse input #{index} for '{program_id}/{function_name}'"))
            })
            .collect::<Result<Vec<_>>>()?;
        lap!(timer, "Prepare inputs");

        // Compute the core logic.
        macro_rules! logic {
            ($process:expr, $network:path, $aleo:path) => {{
                let inputs = inputs.to_vec();

                // Prepare the inputs.
                let private_key = cast_ref!(&private_key as PrivateKey<$network>);
                let program_id = cast_ref!(program_id as ProgramID<$network>);
                let function_name = cast_ref!(function_name as Identifier<$network>);
                let inputs = cast_ref!(inputs as Vec<Value<$network>>);

                // Compute the authorization.
                let authorization =
                    $process.authorize::<$aleo, _>(private_key, program_id, function_name, inputs.iter(), rng)?;
                lap!(timer, "Compute authorization");

                finish!(timer);

                // Return the authorization.
                Ok(cast_ref!(authorization as Authorization<N>).clone())
            }};
        }
        // Process the logic.
        process!(self, logic)
    }
}
