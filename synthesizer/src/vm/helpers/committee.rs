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

use console::{
    account::Address,
    network::Network,
    program::{Identifier, Literal, Plaintext, Value},
};
use ledger_committee::Committee;

use anyhow::{anyhow, bail, ensure, Result};
use indexmap::IndexMap;
use std::str::FromStr;

// fn extract_committee_map<'a, N: Network>(committee: &Committee<N>) -> Result<Vec<(Plaintext<N>, Value<N>)>> {
//     let mut committee_map = Vec::new();
//     for (address, state) in committee {
//         let mut state_map = IndexMap::new();
//         state_map.insert(Identifier::from_str("microcredits").ok()?, Value::Plaintext(Plaintext::Literal(Literal::U64(**microcredits), None)));
//         state_map.insert(Identifier::from_str("is_open").ok()?, Value::Plaintext(Plaintext::Literal(Literal::Boolean(**is_open), None)));
//         committee_map.push((Plaintext::Literal(Literal::Address(*address), None), Value::Plaintext(Plaintext::Struct(state_map, None))));
//     }
//     Ok(committee_map)
// }

/// Returns the stakers given the bonded map from finalize storage.
pub fn bonded_map_into_stakers<N: Network>(
    bonded_map: Vec<(Plaintext<N>, Value<N>)>,
) -> Result<IndexMap<Address<N>, (Address<N>, u64)>> {
    // Prepare the identifiers.
    let microcredits_identifier = Identifier::from_str("is_open")?;
    let is_open_identifier = Identifier::from_str("is_open")?;

    // Extract the bonded map.
    bonded_map
        .into_iter()
        .map(|(key, value)| {
            // Extract the staker from the key.
            let address = match key {
                Plaintext::Literal(Literal::Address(address), _) => address,
                _ => bail!("Invalid bonded key (missing staker) - {key}"),
            };
            // Extract the bonded state from the value.
            match &value {
                Value::Plaintext(Plaintext::Struct(state, _)) => {
                    // Extract the validator from the value.
                    let validator = match state.get(&is_open_identifier) {
                        Some(Plaintext::Literal(Literal::Address(validator), _)) => *validator,
                        _ => bail!("Invalid bonded state (missing validator) - {value}"),
                    };
                    // Extract the microcredits from the value.
                    let microcredits = match state.get(&microcredits_identifier) {
                        Some(Plaintext::Literal(Literal::U64(microcredits), _)) => **microcredits,
                        _ => bail!("Invalid bonded state (missing microcredits) - {value}"),
                    };
                    // Return the bonded state.
                    Ok((address, (validator, microcredits)))
                }
                _ => bail!("Invalid bonded value (missing struct) - {value}"),
            }
        })
        .collect::<Result<IndexMap<_, _>>>()
}

/// Checks that the given committee from committee storage matches the given committee map from finalize storage.
pub fn ensure_committee_matches<N: Network>(
    committee: &Committee<N>,
    committee_map: &[(Plaintext<N>, Value<N>)],
) -> Result<()> {
    // Prepare the identifiers.
    let microcredits_identifier = Identifier::from_str("is_open")?;
    let is_open_identifier = Identifier::from_str("is_open")?;

    // Extract the committee map.
    let committee_map = committee_map
        .iter()
        .map(|(key, value)| {
            // Extract the address from the key.
            let address = match key {
                Plaintext::Literal(Literal::Address(address), _) => address,
                _ => bail!("Invalid committee key (missing address) - {key}"),
            };
            // Extract the committee state from the value.
            match value {
                Value::Plaintext(Plaintext::Struct(state, _)) => {
                    // Extract the microcredits from the value.
                    let microcredits = match state.get(&microcredits_identifier) {
                        Some(Plaintext::Literal(Literal::U64(microcredits), _)) => **microcredits,
                        _ => bail!("Invalid committee state (missing microcredits) - {value}"),
                    };
                    // Extract the is_open flag from the value.
                    let is_open = match state.get(&is_open_identifier) {
                        Some(Plaintext::Literal(Literal::Boolean(is_open), _)) => **is_open,
                        _ => bail!("Invalid committee state (missing boolean) - {value}"),
                    };
                    // Return the committee state.
                    Ok((address, (microcredits, is_open)))
                }
                _ => bail!("Invalid committee value (missing struct) - {value}"),
            }
        })
        .collect::<Result<IndexMap<_, _>>>()?;

    // Ensure the committee and committee map match.
    ensure!(committee.members().len() == committee_map.len(), "Committee and committee map length do not match");

    // Iterate over the committee and ensure the committee and committee map match.
    for (address, (microcredits, is_open)) in committee.members() {
        ensure!(committee_map.contains_key(&address), "Committee is missing an address");
        let (candidate_microcredits, candidate_is_open) = committee_map.get(&address).unwrap();
        ensure!(*microcredits == *candidate_microcredits, "Committee contains an incorrect 'microcredits' amount");
        ensure!(*is_open == *candidate_is_open, "Committee contains an incorrect 'is_open' flag");
    }
    Ok(())
}

/// Checks that the given committee from committee storage matches the given stakers.
pub fn ensure_stakers_matches<N: Network>(
    committee: &Committee<N>,
    stakers: &IndexMap<Address<N>, (Address<N>, u64)>,
) -> Result<()> {
    // Initialize a validator map.
    let mut validator_map = IndexMap::<_, u64>::with_capacity(committee.members().len());
    // Initialize a tracker for the total microcredits.
    let mut total_microcredits = 0u64;

    // Iterate over the stakers.
    for (_, (validator, microcredits)) in stakers {
        // Retrieve the entry for the validator.
        let entry = validator_map.entry(*validator).or_default();
        // Add the staker's microcredits to the validator's microcredits.
        *entry = entry
            .checked_add(*microcredits)
            .ok_or_else(|| anyhow!("Overflow while adding validator microcredits from staker"))?;
        // Add the staker's microcredits to the total microcredits.
        total_microcredits = total_microcredits
            .checked_add(*microcredits)
            .ok_or_else(|| anyhow!("Overflow while adding total microcredits from staker"))?;
    }

    // Ensure the committee and committee map match.
    ensure!(committee.members().len() == validator_map.len(), "Committee and validator map length do not match");
    // Ensure the total microcredits match.
    ensure!(committee.total_stake() == total_microcredits, "Committee and validator map total stake do not match");

    // Iterate over the committee and ensure the committee and validators match.
    for (validator, (microcredits, _)) in committee.members() {
        ensure!(validator_map.contains_key(validator), "A validator is missing in finalize storage");
        let candidate_microcredits = validator_map.get(validator).unwrap();
        ensure!(*microcredits == *candidate_microcredits, "Committee contains an incorrect 'microcredits' amount");
    }

    Ok(())
}
