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

mod cli;
pub use cli::*;

mod commands;
pub use commands::*;

mod errors;
pub use errors::*;

pub mod helpers;
pub use helpers::*;

// TODO (raychu86): DO NOT IMPLEMENT THESE TESTS HERE. Add them to Ledger or Synthesizer.
#[cfg(test)]
mod tests {
    use crate::{
        console::network::TestnetV0,
        ledger::{
            authority::Authority,
            narwhal::{Data, Subdag, Transmission, TransmissionID},
            store::helpers::memory::ConsensusMemory,
            Block,
            Ledger,
        },
    };

    use aleo_std::StorageMode;
    use core::ops::Deref;
    use indexmap::IndexMap;

    fn extract_transmissions(block: &Block<TestnetV0>) -> IndexMap<TransmissionID<TestnetV0>, Transmission<TestnetV0>> {
        let mut transmissions = IndexMap::new();
        for tx in block.transactions().iter() {
            let checksum = Data::Object(tx.transaction().clone()).to_checksum::<TestnetV0>().unwrap();
            transmissions.insert(TransmissionID::from((&tx.id(), &checksum)), tx.transaction().clone().into());
        }
        if let Some(coinbase_solution) = block.solutions().as_ref() {
            for (_, solution) in coinbase_solution.iter() {
                let checksum = Data::Object(*solution).to_checksum::<TestnetV0>().unwrap();
                transmissions.insert(TransmissionID::from((solution.id(), checksum)), (*solution).into());
            }
        }
        transmissions
    }

    #[test]
    fn test_forged_block() {
        // TODO (raychu86): DO NOT USE REAL BLOCKS. CREATE BLOCKS FROM SCRATCH FOR TESTING.
        let genesis: Block<TestnetV0> =
            ureq::get("https://api.explorer.aleo.org/v1/testnet/block/0").call().unwrap().into_json().unwrap();
        let block_1: Block<TestnetV0> =
            ureq::get("https://api.explorer.aleo.org/v1/testnet/block/1").call().unwrap().into_json().unwrap();
        let block_2: Block<TestnetV0> =
            ureq::get("https://api.explorer.aleo.org/v1/testnet/block/2").call().unwrap().into_json().unwrap();
        let block_3: Block<TestnetV0> =
            ureq::get("https://api.explorer.aleo.org/v1/testnet/block/3").call().unwrap().into_json().unwrap();

        let ledger =
            Ledger::<TestnetV0, ConsensusMemory<TestnetV0>>::load(genesis.clone(), StorageMode::Development(111))
                .unwrap();
        ledger.advance_to_next_block(&block_1).unwrap();

        ////////////////////////////////////////////////////////////////////////////
        // Attack 1: Forge block 2' with the subdag of block 3.
        ////////////////////////////////////////////////////////////////////////////
        {
            println!("PERFORMING ATTACK 1: FORGING BLOCK 2' WITH THE SUBDAG OF BLOCK 3");

            let block_3_subdag =
                if let Authority::Quorum(subdag) = block_3.authority() { subdag } else { unreachable!("") };

            // Fetch the transmissions.
            let transmissions = extract_transmissions(&block_3);

            // Forge the block.
            let forged_block_2 = ledger
                .prepare_advance_to_next_quorum_block(block_3_subdag.clone(), transmissions, &mut rand::thread_rng())
                .unwrap();

            assert_ne!(forged_block_2, block_2);

            // Attempt to verify the forged block.
            assert!(ledger.check_next_block(&forged_block_2, &mut rand::thread_rng()).is_err());
        }

        ////////////////////////////////////////////////////////////////////////////
        // Attack 2: Forge block 2' with the combined subdag of block 2 and 3.
        ////////////////////////////////////////////////////////////////////////////
        {
            println!("PERFORMING ATTACK 2: FORGING BLOCK 2' WITH THE COMBINED SUBDAG OF BLOCK 2 AND 3");

            // Fetch the subdags.
            let block_2_subdag =
                if let Authority::Quorum(subdag) = block_2.authority() { subdag } else { unreachable!("") };
            let block_3_subdag =
                if let Authority::Quorum(subdag) = block_3.authority() { subdag } else { unreachable!("") };

            // Combined the subdags.
            let mut combined_subdag = block_2_subdag.deref().clone();
            for (round, certificates) in block_3_subdag.iter() {
                combined_subdag
                    .entry(*round)
                    .and_modify(|c| c.extend(certificates.clone()))
                    .or_insert(certificates.clone());
            }

            // Fetch the transmissions.
            let block_2_transmissions = extract_transmissions(&block_2);
            let block_3_transmissions = extract_transmissions(&block_3);

            // Combine the transmissions.
            let mut combined_transmissions = block_2_transmissions;
            combined_transmissions.extend(block_3_transmissions);

            // Forge the block.
            let forged_block_2_from_both_subdags = ledger
                .prepare_advance_to_next_quorum_block(
                    Subdag::from(combined_subdag).unwrap(),
                    combined_transmissions,
                    &mut rand::thread_rng(),
                )
                .unwrap();

            assert_ne!(forged_block_2_from_both_subdags, block_1);

            // Attempt to verify the forged block.
            assert!(ledger.check_next_block(&forged_block_2_from_both_subdags, &mut rand::thread_rng()).is_err());
        }
    }
}
