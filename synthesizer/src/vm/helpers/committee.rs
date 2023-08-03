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
    types::{Boolean, U64},
};
use ledger_committee::Committee;

use anyhow::{anyhow, bail, ensure, Result};
use indexmap::{indexmap, IndexMap};
use std::str::FromStr;

/// Returns the stakers given the bonded map from finalize storage.
pub fn bonded_map_into_stakers<N: Network>(
    bonded_map: Vec<(Plaintext<N>, Value<N>)>,
) -> Result<IndexMap<Address<N>, (Address<N>, u64)>> {
    // Prepare the identifiers.
    let validator_identifier = Identifier::from_str("validator")?;
    let microcredits_identifier = Identifier::from_str("microcredits")?;

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
                    let validator = match state.get(&validator_identifier) {
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
    let microcredits_identifier = Identifier::from_str("microcredits")?;
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

/// Returns the next committee, given the current committee and stakers.
pub fn to_next_committee<N: Network>(
    current_committee: &Committee<N>,
    next_round: u64,
    next_stakers: &IndexMap<Address<N>, (Address<N>, u64)>,
) -> Result<Committee<N>> {
    // Initialize the validators.
    let mut validators = IndexMap::<_, u64>::with_capacity(current_committee.members().len());

    for (_, (validator, microcredits)) in next_stakers {
        // Retrieve the entry for the validator.
        let entry = validators.entry(*validator).or_default();
        // Add the staker's microcredits to the validator's microcredits.
        *entry = entry
            .checked_add(*microcredits)
            .ok_or_else(|| anyhow!("Overflow while adding validator microcredits from staker"))?;
    }

    // Initialize the members.
    let mut members = IndexMap::with_capacity(validators.len());
    // Iterate over the validators.
    for (validator, microcredits) in validators {
        members.insert(validator, (microcredits, current_committee.is_committee_member_open(validator)));
    }
    // Return the next committee.
    Committee::new(next_round, members)
}

/// Returns the committee map and bonded map, given the committee and stakers.
pub fn to_next_commitee_map_and_bonded_map<N: Network>(
    next_committee: &Committee<N>,
    next_stakers: &IndexMap<Address<N>, (Address<N>, u64)>,
) -> (Vec<(Plaintext<N>, Value<N>)>, Vec<(Plaintext<N>, Value<N>)>) {
    // Prepare the identifiers.
    let validator_identifier = Identifier::from_str("validator").expect("Failed to parse 'validator'");
    let microcredits_identifier = Identifier::from_str("microcredits").expect("Failed to parse 'microcredits'");
    let is_open_identifier = Identifier::from_str("is_open").expect("Failed to parse 'is_open'");

    // Initialize the committee map.
    let mut committee_map = Vec::with_capacity(next_committee.members().len());
    // Initialize the bonded map.
    let mut bonded_map = Vec::with_capacity(next_stakers.len());

    for (staker, (validator, microcredits)) in next_stakers {
        // Construct the bonded state.
        let bonded_state = indexmap! {
            validator_identifier => Plaintext::from(Literal::Address(*validator)),
            microcredits_identifier => Plaintext::from(Literal::U64(U64::new(*microcredits))),
        };
        // Update the bonded map.
        bonded_map.push((
            Plaintext::from(Literal::Address(*staker)),
            Value::Plaintext(Plaintext::Struct(bonded_state, Default::default())),
        ));
    }

    for (validator, (microcredits, is_open)) in next_committee.members() {
        // Construct the committee state.
        let committee_state = indexmap! {
            microcredits_identifier => Plaintext::from(Literal::U64(U64::new(*microcredits))),
            is_open_identifier => Plaintext::from(Literal::Boolean(Boolean::new(*is_open))),
        };
        // Update the committee map.
        committee_map.push((
            Plaintext::from(Literal::Address(*validator)),
            Value::Plaintext(Plaintext::Struct(committee_state, Default::default())),
        ));
    }

    (committee_map, bonded_map)
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::prelude::TestRng;
    use ledger_committee::MIN_STAKE;

    use rand::Rng;
    use rayon::prelude::*;
    use std::str::FromStr;

    type CurrentNetwork = console::network::Testnet3;

    const ITERATIONS: usize = 1000;

    /// Returns the committee map, given the map of `(validator, (microcredits, is_open))` entries.
    fn to_committee_map<N: Network>(members: &IndexMap<Address<N>, (u64, bool)>) -> Vec<(Plaintext<N>, Value<N>)> {
        let mut committee_map = Vec::with_capacity(members.len());

        for (validator, (microcredits, is_open)) in members {
            let microcredits = U64::<N>::new(*microcredits);
            let is_open = Boolean::<N>::new(*is_open);

            committee_map.push((
                Plaintext::from(Literal::Address(*validator)),
                Value::from_str(&format!("{{ microcredits: {microcredits}, is_open: {is_open} }}")).unwrap(),
            ));
        }
        committee_map
    }

    /// Returns the bonded map, given the staker, validator and microcredits.
    fn to_bonded_map<N: Network>(stakers: &IndexMap<Address<N>, (Address<N>, u64)>) -> Vec<(Plaintext<N>, Value<N>)> {
        let mut bonded_map = Vec::with_capacity(stakers.len());

        for (staker, (validator, microcredits)) in stakers {
            let microcredits = U64::<N>::new(*microcredits);

            bonded_map.push((
                Plaintext::from(Literal::Address(*staker)),
                Value::from_str(&format!("{{ validator: {validator}, microcredits: {microcredits} }}")).unwrap(),
            ));
        }
        bonded_map
    }

    /// Returns the stakers, given the map of `(validator, (microcredits, is_open))` entries.
    /// This method simulates the existence of delegators for the members.
    fn to_stakers<N: Network>(members: &IndexMap<Address<N>, (u64, bool)>) -> IndexMap<Address<N>, (Address<N>, u64)> {
        members
            .into_par_iter()
            .flat_map(|(validator, (microcredits, _))| {
                let rng = &mut TestRng::default();

                let mut stakers = IndexMap::new();

                // Insert the validator.
                stakers.insert(*validator, (*validator, MIN_STAKE));

                // Keep a tally of the remaining microcredits.
                let mut remaining_microcredits = microcredits.saturating_sub(MIN_STAKE);

                // Set the staker amount to 1 credit.
                let staker_amount = 1_000_000;

                while remaining_microcredits > 2 * staker_amount {
                    // Sample a random staker.
                    let staker = Address::<N>::new(rng.gen());
                    // Insert staker.
                    stakers.insert(staker, (*validator, staker_amount));
                    // Update the remaining microcredits.
                    remaining_microcredits = remaining_microcredits - staker_amount;
                }

                // Insert the last staker.
                let staker = Address::<N>::new(rng.gen());
                stakers.insert(staker, (*validator, remaining_microcredits));

                stakers
            })
            .collect()
    }

    #[test]
    fn test_bonded_map_into_stakers() {
        let rng = &mut TestRng::default();

        for _ in 0..ITERATIONS {
            let staker = Address::<CurrentNetwork>::new(rng.gen());
            let validator = Address::<CurrentNetwork>::new(rng.gen());
            let microcredits = U64::<CurrentNetwork>::new(rng.gen());

            // Initialize the bonded map.
            let bonded_map = to_bonded_map(&indexmap::indexmap! {
                staker => (validator, *microcredits),
            });

            // Convert the bonded map into stakers.
            let stakers = bonded_map_into_stakers(bonded_map).unwrap();
            assert_eq!(stakers.len(), 1);
            assert_eq!(stakers.get(&staker).unwrap(), &(validator, *microcredits));
        }
    }

    #[test]
    fn test_ensure_committee_matches() {
        let rng = &mut TestRng::default();

        for _ in 0..ITERATIONS {
            // Sample a committee.
            let committee = ledger_committee::test_helpers::sample_committee(rng);
            // Convert the committee into a committee map.
            let committee_map = to_committee_map(committee.members());

            // Ensure the committee matches.
            let result = ensure_committee_matches(&committee, &committee_map);
            assert!(result.is_ok());
        }
    }

    #[test]
    fn test_ensure_stakers_matches() {
        let rng = &mut TestRng::default();

        // Sample a committee.
        let committee = ledger_committee::test_helpers::sample_committee(rng);
        // Convert the committee into stakers.
        let stakers = to_stakers(committee.members());

        // Start a timer.
        let timer = std::time::Instant::now();
        // Ensure the stakers matches.
        let result = ensure_stakers_matches(&committee, &stakers);
        println!("ensure_stakers_matches: {}ms", timer.elapsed().as_millis());
        assert!(result.is_ok());
    }

    #[test]
    fn test_to_next_committee() {
        let rng = &mut TestRng::default();

        // Sample a committee.
        let committee = ledger_committee::test_helpers::sample_committee(rng);
        // Convert the committee into stakers.
        let stakers = to_stakers(committee.members());

        // Start a timer.
        let timer = std::time::Instant::now();
        // Ensure the next committee matches the current committee.
        // Note: We can perform this check, in this specific case only, because we did not apply staking rewards.
        let next_committee = to_next_committee(&committee, committee.starting_round() + 1, &stakers).unwrap();
        println!("to_next_committee: {}ms", timer.elapsed().as_millis());
        assert_eq!(committee.starting_round() + 1, next_committee.starting_round());
        assert_eq!(committee.members(), next_committee.members());
    }
}
