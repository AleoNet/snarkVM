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

#[cfg(feature = "console")]
pub use snarkvm_console as console;
#[cfg(feature = "curves")]
pub use snarkvm_curves as curves;
#[cfg(feature = "fields")]
pub use snarkvm_fields as fields;
#[cfg(feature = "synthesizer")]
pub use snarkvm_synthesizer as synthesizer;
#[cfg(feature = "utilities")]
pub use snarkvm_utilities as utilities;

#[cfg(test)]
mod tests {
    use super::*;
    use rand::Rng;
    use snarkvm_circuit_network::AleoV0;
    use snarkvm_console::{
        account::{Address, PrivateKey},
        network::Testnet3,
        program::{Field, Plaintext, Record},
    };
    use snarkvm_synthesizer::Process;
    use snarkvm_utilities::{TestRng, Uniform};
    use std::str::FromStr;
    use wasm_bindgen_test::*;

    pub type CurrentNetwork = Testnet3;
    pub type CurrentAleo = AleoV0;

    #[wasm_bindgen_test]
    async fn test_execute_fee_private_async() {
        let rng = &mut TestRng::default();

        // Initialize the process.
        let process = Process::<CurrentNetwork>::load_web().unwrap();

        // Sample a private key.
        let private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
        let owner = Address::try_from(private_key).unwrap();
        // Sample a fee in microcredits.
        let fee_in_microcredits = rng.gen();
        // Sample a credits record.
        let credits = Record::<CurrentNetwork, Plaintext<_>>::from_str(&format!(
            "{{ owner: {owner}.private, microcredits: {fee_in_microcredits}u64.private, _nonce: 0group.public }}"
        ))
        .unwrap();
        // Sample a deployment or execution ID.
        let deployment_or_execution_id = Field::rand(rng);

        // Initialize the authorization.
        let authorization = process
            .authorize_fee_private(&private_key, credits, fee_in_microcredits, deployment_or_execution_id, rng)
            .unwrap();
        assert!(authorization.is_fee_private(), "Authorization must be for a call to 'credits.aleo/fee_private'");

        // Execute the authorization.
        let (response, trace) = process.execute_async::<CurrentAleo>(authorization).await.unwrap();
        // Ensure the response has 1 output.
        assert_eq!(response.outputs().len(), 1, "Execution of 'credits.aleo/fee_private' must contain 1 output");
        // Ensure the response has 1 output ID.
        assert_eq!(response.output_ids().len(), 1, "Execution of 'credits.aleo/fee_private' must contain 1 output ID");
        // Ensure the trace contains 1 transition.
        assert_eq!(trace.transitions().len(), 1, "Execution of 'credits.aleo/fee_private' must contain 1 transition");

        // Retrieve the transition.
        let transition = trace.transitions()[0].clone();
        assert!(transition.is_fee_private(), "Transition must be for 'credits.aleo/fee_private'");
    }
}
