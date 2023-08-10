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

use crate::Process;
use circuit::network::AleoV0;
use console::{
    account::{Address, PrivateKey},
    network::{prelude::*, Testnet3},
    program::{Identifier, Literal, Plaintext, ProgramID, Value},
};
use ledger_query::Query;
use ledger_store::{
    helpers::memory::{BlockMemory, FinalizeMemory},
    BlockStore,
    FinalizeStore,
};
use synthesizer_program::{FinalizeGlobalState, FinalizeStoreTrait};

use indexmap::IndexMap;

type CurrentNetwork = Testnet3;
type CurrentAleo = AleoV0;

/// Samples a new finalize state.
fn sample_finalize_state(block_height: u32) -> FinalizeGlobalState {
    FinalizeGlobalState::from(block_height, [0u8; 32])
}

/// Get the current `account` mapping balance.
fn account_balance(
    finalize_store: &FinalizeStore<CurrentNetwork, FinalizeMemory<CurrentNetwork>>,
    address: &Address<CurrentNetwork>,
) -> Result<u64> {
    // Initialize the program ID, mapping name, and key.
    let program_id = ProgramID::from_str("credits.aleo")?;
    let mapping = Identifier::from_str("account")?;
    let key = Plaintext::from(Literal::Address(*address));

    // Retrieve the balance from the finalize store.
    match finalize_store.get_value_confirmed(&program_id, &mapping, &key)? {
        Some(Value::Plaintext(Plaintext::Literal(Literal::U64(balance), _))) => Ok(*balance),
        _ => bail!("Account balance not found for: {address}"),
    }
}

/// Get the current committee state from the `committee` mapping for the given validator address.
/// Returns the `committee_state` as a tuple of `(microcredits, is_open)`.
fn committee_state(
    finalize_store: &FinalizeStore<CurrentNetwork, FinalizeMemory<CurrentNetwork>>,
    address: &Address<CurrentNetwork>,
) -> Result<(u64, bool)> {
    // Initialize the program ID, mapping name, and key.
    let program_id = ProgramID::from_str("credits.aleo")?;
    let mapping = Identifier::from_str("committee")?;
    let key = Plaintext::from(Literal::Address(*address));

    // Retrieve the committee state from the finalize store.
    let state = match finalize_store.get_value_confirmed(&program_id, &mapping, &key)? {
        Some(Value::Plaintext(Plaintext::Struct(state, _))) => state,
        _ => bail!("Account balance not found for: {address}"),
    };

    // Retrieve `microcredits` from the committee state.
    let microcredits = match state.get(&Identifier::from_str("microcredits")?) {
        Some(Plaintext::Literal(Literal::U64(microcredits), _)) => **microcredits,
        _ => bail!("`microcredits` not found for: {address}"),
    };

    // Retrieve `is_open` from the committee state.
    let is_open = match state.get(&Identifier::from_str("is_open")?) {
        Some(Plaintext::Literal(Literal::Boolean(is_open), _)) => **is_open,
        _ => bail!("`is_open` not found for: {address}"),
    };

    Ok((microcredits, is_open))
}

/// Get the current bond state from the `bonding` mapping for the given staker address.
/// Returns the `committee_state` as a tuple of `(validator address, microcredits)`.
fn bond_state(
    finalize_store: &FinalizeStore<CurrentNetwork, FinalizeMemory<CurrentNetwork>>,
    address: &Address<CurrentNetwork>,
) -> Result<(Address<CurrentNetwork>, u64)> {
    // Initialize the program ID, mapping name, and key.
    let program_id = ProgramID::from_str("credits.aleo")?;
    let mapping = Identifier::from_str("bonded")?;
    let key = Plaintext::from(Literal::Address(*address));

    // Retrieve the bond state from the finalize store.
    let state = match finalize_store.get_value_confirmed(&program_id, &mapping, &key)? {
        Some(Value::Plaintext(Plaintext::Struct(state, _))) => state,
        _ => bail!("Account balance not found for: {address}"),
    };

    // Retrieve `validator` from the bond state.
    let validator = match state.get(&Identifier::from_str("validator")?) {
        Some(Plaintext::Literal(Literal::Address(address), _)) => *address,
        _ => bail!("`validator` not found for: {address}"),
    };

    // Retrieve `microcredits` from the bond state.
    let microcredits = match state.get(&Identifier::from_str("microcredits")?) {
        Some(Plaintext::Literal(Literal::U64(microcredits), _)) => **microcredits,
        _ => bail!("`microcredits` not found for: {address}"),
    };

    Ok((validator, microcredits))
}

/// Initializes the validator and delegator balances in the finalize store.
/// Returns the private keys and balances for the validators and delegators.
fn initialize_stakers(
    finalize_store: &FinalizeStore<CurrentNetwork, FinalizeMemory<CurrentNetwork>>,
    num_validators: u32,
    num_delegators: u32,
    rng: &mut TestRng,
) -> Result<(
    IndexMap<PrivateKey<CurrentNetwork>, (Address<CurrentNetwork>, u64)>,
    IndexMap<PrivateKey<CurrentNetwork>, (Address<CurrentNetwork>, u64)>,
)> {
    let program_id = ProgramID::from_str("credits.aleo")?;
    let accounts_mapping = Identifier::from_str("account")?;

    let mut validators: IndexMap<_, _> = Default::default();
    let mut delegators: IndexMap<_, _> = Default::default();

    // Initialize the balances for the validators and delegators.
    for i in 0..(num_validators + num_delegators) {
        // Initialize a new account.
        let private_key = PrivateKey::<CurrentNetwork>::new(rng)?;
        let address = Address::try_from(&private_key)?;
        let balance = 10_000_000_000_000u64;

        let key = Plaintext::from(Literal::Address(address));
        let value = Value::from_str(&format!("{balance}u64"))?;

        // Add the balance directly to the finalize store.
        finalize_store.insert_key_value(&program_id, &accounts_mapping, key, value)?;

        if i < num_validators {
            // Insert the validator into the list of validators.
            validators.insert(private_key, (address, balance));
        } else {
            // Insert the delegator into the list of delegators.
            delegators.insert(private_key, (address, balance));
        }
    }

    Ok((validators, delegators))
}

/// Perform a bond public execution.
fn bond(
    process: &Process<CurrentNetwork>,
    finalize_store: &FinalizeStore<CurrentNetwork, FinalizeMemory<CurrentNetwork>>,
    caller_private_key: &PrivateKey<CurrentNetwork>,
    validator_address: &Address<CurrentNetwork>,
    amount: u64,
    rng: &mut TestRng,
) -> Result<()> {
    // Construct the execution.
    let inputs = [validator_address.to_string(), format!("{amount}_u64")];

    // Construct the authorization.
    let authorization =
        process.authorize::<CurrentAleo, _>(caller_private_key, "credits.aleo", "bond_public", inputs.iter(), rng)?;

    // Construct the trace.
    let (_, mut trace) = process.execute::<CurrentAleo>(authorization)?;

    // Construct the block store.
    let block_store = BlockStore::<CurrentNetwork, BlockMemory<_>>::open(None)?;

    // Prepare the trace.
    trace.prepare(Query::from(&block_store))?;

    // Prove the execution.
    let execution = trace.prove_execution::<CurrentAleo, _>("bond_public", rng)?;

    // Finalize the execution.
    process.finalize_execution(sample_finalize_state(1), finalize_store, &execution)?;

    Ok(())
}

// TODO (raychu86): Separate these cases into individual tests.
#[test]
fn test_bond_validator() {
    let rng = &mut TestRng::default();

    // Construct the process.
    let process = Process::<CurrentNetwork>::load().unwrap();

    // Initialize a new finalize store.
    let finalize_store = FinalizeStore::<CurrentNetwork, FinalizeMemory<_>>::open(None).unwrap();

    // Initialize the validators and delegators.
    let (validators, _) = initialize_stakers(&finalize_store, 6, 0, rng).unwrap();
    let mut validators = validators.into_iter();

    // Ensure bonding a new validator with more than 1_000_000_000_000 microcredits succeeds.
    {
        let (validator_private_key, (validator_address, _)) = validators.next().unwrap();

        // Fetch the account balance.
        let public_balance = account_balance(&finalize_store, &validator_address).unwrap();

        // Perform the bond.
        let amount = 1_000_000_000_000u64;
        bond(&process, &finalize_store, &validator_private_key, &validator_address, amount, rng).unwrap();

        // Check that the balances are correct.
        let new_public_balance = account_balance(&finalize_store, &validator_address).unwrap();
        assert_eq!(public_balance - amount, new_public_balance);
        assert_eq!(committee_state(&finalize_store, &validator_address).unwrap(), (amount, true));
        assert_eq!(bond_state(&finalize_store, &validator_address).unwrap(), (validator_address, amount));
    }

    // Ensure bonding a new validator with less than 1_000_000_000_000 microcredits fails.
    {
        let (validator_private_key, (validator_address, _)) = validators.next().unwrap();
        assert!(
            bond(
                &process,
                &finalize_store,
                &validator_private_key,
                &validator_address,
                rng.gen_range(1..1_000_000_000_000u64),
                rng
            )
            .is_err()
        );
    }

    // Ensure bonding an amount larger than the account balance will fail.
    {
        let (validator_private_key, (validator_address, _)) = validators.next().unwrap();

        // Fetch the account balance.
        let public_balance = account_balance(&finalize_store, &validator_address).unwrap();

        assert!(
            bond(&process, &finalize_store, &validator_private_key, &validator_address, public_balance + 1, rng)
                .is_err()
        );
    }

    // Ensure that adding additional bond succeeds.
    {
        let (validator_private_key, (validator_address, _)) = validators.next().unwrap();

        // Fetch the account balance.
        let public_balance = account_balance(&finalize_store, &validator_address).unwrap();

        // Perform the bond.
        let amount = 1_000_000_000_000u64;
        bond(&process, &finalize_store, &validator_private_key, &validator_address, amount, rng).unwrap();

        // Perform another bond.
        bond(&process, &finalize_store, &validator_private_key, &validator_address, amount, rng).unwrap();

        // Check that the balances are correct.
        let new_public_balance = account_balance(&finalize_store, &validator_address).unwrap();
        assert_eq!(public_balance - amount * 2, new_public_balance);
        assert_eq!(committee_state(&finalize_store, &validator_address).unwrap(), (amount * 2, true));
        assert_eq!(bond_state(&finalize_store, &validator_address).unwrap(), (validator_address, amount * 2));
    }

    // Ensure that bonding to another validator fails.
    {
        let (validator_private_key_1, (validator_address_1, _)) = validators.next().unwrap();
        let (validator_private_key_2, (validator_address_2, _)) = validators.next().unwrap();

        // Perform the bond for validator 1.
        let amount = 1_000_000_000_000u64;
        bond(&process, &finalize_store, &validator_private_key_1, &validator_address_1, amount, rng).unwrap();

        // Perform the bond for validator 2.
        bond(&process, &finalize_store, &validator_private_key_2, &validator_address_2, amount, rng).unwrap();

        // Ensure that bonding to another validator fails.
        assert!(bond(&process, &finalize_store, &validator_private_key_1, &validator_address_2, amount, rng).is_err());
    }
}

#[test]
fn test_bond_delegator() {}

// Test cases:

//    bond_public:
//    Validator bonds over 1M credits succeeds. -
//    Validator bond under 1M credits fails. -
//    Validator bonds to existing balance succeeds -
//    Validator bonds more than his `account` balance fails. -
//    Validator bonds to another validator fails. -
//
//    Delegator bonds under 1 credit fails.
//    Delegator bonds to existing validator succeeds.
//    Delegator bonds to non-existing validator fails.
//    Delegator bonds to multiple validator fails.

//   set_validator_state:
//   Validator can't bond to himself if closed.
//   Delegator can't bond to closed validator.

//  unbond_delegator_as_validator:
//  Validator can unbond delegator if closed.
//  Validator can't unbond delegator that is not bonded to him.
//  Validator can't unbond delegator if open.

//  unbond_public:
//  Validator can unbond if remaining balance is more than 1M.
//  Validator can unbond if there is no remaining balance and there are no delegators.
//  Validator can't unbond more than his stake.
//  Validator can't unbond if remaining balance is less than 1M.
//  Validator can't unbond all stake if there are still delegators.
//
//  Delegator can unbond balance if remaining is greater than 1 credit.
//  Delegator can unbond balance if there is no remaining balance.
//  Delegator can't unbond more than his stake.
//  Delegator can't unbond if the remaining balance is less than 1 credit.

//  Check that Validator/Delegator Unbonding updates the unbond height and updates the balance correctly.

// claim_unbond:
// Staker can claim unbond if the unbonding period has passed.
// Staker can't claim unbond if the unbonding period has not passed.
