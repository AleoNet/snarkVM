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
    types::U64,
};
use ledger_committee::{MIN_DELEGATOR_STAKE, MIN_VALIDATOR_STAKE};
use ledger_query::Query;
use ledger_store::{
    atomic_finalize,
    helpers::memory::{BlockMemory, FinalizeMemory},
    BlockStore,
    FinalizeMode,
    FinalizeStore,
};
use synthesizer_program::{FinalizeGlobalState, FinalizeStoreTrait, Program};

use indexmap::IndexMap;

type CurrentNetwork = Testnet3;
type CurrentAleo = AleoV0;

const NUM_BLOCKS_TO_UNLOCK: u32 = 720;

/// Samples a new finalize state.
fn sample_finalize_state(block_height: u32) -> FinalizeGlobalState {
    FinalizeGlobalState::from(block_height as u64, block_height, [0u8; 32])
}

/// Returns the `value` for the given `key` in the `mapping` for the given `program_id`.
fn get_mapping_value<N: Network>(
    store: &FinalizeStore<N, FinalizeMemory<N>>,
    program_id: &str,
    mapping: &str,
    key: Literal<N>,
) -> Result<Option<Value<N>>> {
    // Prepare the program ID, mapping name, and key.
    let program_id = ProgramID::from_str(program_id)?;
    let mapping = Identifier::from_str(mapping)?;
    let key = Plaintext::from(key);
    // Retrieve the value from the finalize store.
    match store.get_value_speculative(&program_id, &mapping, &key) {
        Ok(result) => Ok(result),
        Err(err) => bail!("Error getting value for program_id: {program_id}, mapping: {mapping}, key: {key}: {err}"),
    }
}

/// Get the current `account` mapping balance.
fn account_balance<N: Network>(store: &FinalizeStore<N, FinalizeMemory<N>>, address: &Address<N>) -> Result<u64> {
    // Retrieve the balance from the finalize store.
    match get_mapping_value(store, "credits.aleo", "account", Literal::Address(*address))? {
        Some(Value::Plaintext(Plaintext::Literal(Literal::U64(balance), _))) => Ok(*balance),
        _ => bail!("Missing or malformed account balance for {address}"),
    }
}

/// Get the current committee state from the `committee` mapping for the given validator address.
/// Returns the `committee_state` as a tuple of `(microcredits, is_open)`.
fn committee_state<N: Network>(
    store: &FinalizeStore<N, FinalizeMemory<N>>,
    address: &Address<N>,
) -> Result<Option<(u64, bool)>> {
    // Retrieve the committee state from the finalize store.
    let state = match get_mapping_value(store, "credits.aleo", "committee", Literal::Address(*address))? {
        Some(Value::Plaintext(Plaintext::Struct(state, _))) => state,
        None => return Ok(None),
        _ => bail!("Malformed committee state for {address}"),
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

    Ok(Some((microcredits, is_open)))
}

/// Get the current bond state from the `bonding` mapping for the given staker address.
/// Returns the `bond_state` as a tuple of `(validator address, microcredits)`.
fn bond_state<N: Network>(
    store: &FinalizeStore<N, FinalizeMemory<N>>,
    address: &Address<N>,
) -> Result<Option<(Address<N>, u64)>> {
    // Retrieve the bond state from the finalize store.
    let state = match get_mapping_value(store, "credits.aleo", "bonded", Literal::Address(*address))? {
        Some(Value::Plaintext(Plaintext::Struct(state, _))) => state,
        None => return Ok(None),
        _ => bail!("Malformed bond state for {address}"),
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

    Ok(Some((validator, microcredits)))
}

/// Get the current unbonding state from the `unbonding` mapping for the given staker address.
/// Returns the `unbond_state` as a tuple of `(microcredits, unbond_height)`.
fn unbond_state<N: Network>(
    store: &FinalizeStore<N, FinalizeMemory<N>>,
    address: &Address<N>,
) -> Result<Option<(u64, u32)>> {
    // Retrieve the unbond state from the finalize store.
    let state = match get_mapping_value(store, "credits.aleo", "unbonding", Literal::Address(*address))? {
        Some(Value::Plaintext(Plaintext::Struct(state, _))) => state,
        None => return Ok(None),
        _ => bail!("Malformed unbond state for {address}"),
    };

    // Retrieve `microcredits` from the bond state.
    let microcredits = match state.get(&Identifier::from_str("microcredits")?) {
        Some(Plaintext::Literal(Literal::U64(microcredits), _)) => **microcredits,
        _ => bail!("`microcredits` not found for: {address}"),
    };

    // Retrieve `height` from the bond state.
    let height = match state.get(&Identifier::from_str("height")?) {
        Some(Plaintext::Literal(Literal::U32(height), _)) => **height,
        _ => bail!("`height` not found for: {address}"),
    };

    Ok(Some((microcredits, height)))
}

/// Initializes the validator and delegator balances in the finalize store.
/// Returns the private keys and balances for the validators and delegators.
fn initialize_stakers<N: Network>(
    finalize_store: &FinalizeStore<N, FinalizeMemory<N>>,
    num_validators: u32,
    num_delegators: u32,
    rng: &mut TestRng,
) -> Result<(IndexMap<PrivateKey<N>, (Address<N>, u64)>, IndexMap<PrivateKey<N>, (Address<N>, u64)>)> {
    // Initialize the store for 'credits.aleo'.
    let program = Program::<N>::credits()?;
    for mapping in program.mappings().values() {
        // Ensure that all mappings are initialized.
        if !finalize_store.contains_mapping_confirmed(program.id(), mapping.name())? {
            // Initialize the mappings for 'credits.aleo'.
            finalize_store.initialize_mapping(program.id(), mapping.name())?;
        }
    }

    let mapping = Identifier::from_str("account")?;

    let mut validators: IndexMap<_, _> = Default::default();
    let mut delegators: IndexMap<_, _> = Default::default();

    // Initialize the balances for the validators and delegators.
    for i in 0..(num_validators + num_delegators) {
        // Initialize a new account.
        let private_key = PrivateKey::<N>::new(rng)?;
        let address = Address::try_from(&private_key)?;
        let balance = 10_000_000_000_000u64;

        // Add the balance directly to the finalize store.
        let key = Plaintext::from(Literal::Address(address));
        let value = Value::from(Literal::U64(U64::new(balance)));
        finalize_store.insert_key_value(program.id(), &mapping, key, value)?;
        assert_eq!(balance, account_balance(finalize_store, &address).unwrap());

        // Store the validator or delegator.
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

fn execute_function(
    process: &Process<CurrentNetwork>,
    finalize_store: &FinalizeStore<CurrentNetwork, FinalizeMemory<CurrentNetwork>>,
    caller_private_key: &PrivateKey<CurrentNetwork>,
    function: &str,
    inputs: &[String],
    block_height: Option<u32>,
    rng: &mut TestRng,
) -> Result<()> {
    // Construct the authorization.
    let authorization =
        process.authorize::<CurrentAleo, _>(caller_private_key, "credits.aleo", function, inputs.iter(), rng)?;

    // Construct the trace.
    let (_, mut trace) = process.execute::<CurrentAleo>(authorization)?;

    // Construct the block store.
    let block_store = BlockStore::<CurrentNetwork, BlockMemory<_>>::open(None)?;

    // Prepare the trace.
    trace.prepare(Query::from(&block_store))?;

    // Prove the execution.
    let execution = trace.prove_execution::<CurrentAleo, _>(function, rng)?;

    // Finalize the execution.
    let block_height = block_height.unwrap_or(1);

    // Add an atomic finalize wrapper around the finalize function.
    process.finalize_execution(sample_finalize_state(block_height), finalize_store, &execution)?;

    Ok(())
}

/// Perform a `bond_public`.
fn bond_public(
    process: &Process<CurrentNetwork>,
    finalize_store: &FinalizeStore<CurrentNetwork, FinalizeMemory<CurrentNetwork>>,
    caller_private_key: &PrivateKey<CurrentNetwork>,
    validator_address: &Address<CurrentNetwork>,
    amount: u64,
    rng: &mut TestRng,
) -> Result<()> {
    execute_function(
        process,
        finalize_store,
        caller_private_key,
        "bond_public",
        &[validator_address.to_string(), format!("{amount}_u64")],
        None,
        rng,
    )
}

/// Perform an `unbond_public`.
fn unbond_public(
    process: &Process<CurrentNetwork>,
    finalize_store: &FinalizeStore<CurrentNetwork, FinalizeMemory<CurrentNetwork>>,
    caller_private_key: &PrivateKey<CurrentNetwork>,
    amount: u64,
    block_height: u32,
    rng: &mut TestRng,
) -> Result<()> {
    execute_function(
        process,
        finalize_store,
        caller_private_key,
        "unbond_public",
        &[format!("{amount}_u64")],
        Some(block_height),
        rng,
    )
}

/// Perform a `set_validator_state`.
fn set_validator_state(
    process: &Process<CurrentNetwork>,
    finalize_store: &FinalizeStore<CurrentNetwork, FinalizeMemory<CurrentNetwork>>,
    caller_private_key: &PrivateKey<CurrentNetwork>,
    is_open: bool,
    rng: &mut TestRng,
) -> Result<()> {
    execute_function(
        process,
        finalize_store,
        caller_private_key,
        "set_validator_state",
        &[format!("{is_open}")],
        None,
        rng,
    )
}

/// Perform an `unbond_delegator_as_validator`
fn unbond_delegator_as_validator(
    process: &Process<CurrentNetwork>,
    finalize_store: &FinalizeStore<CurrentNetwork, FinalizeMemory<CurrentNetwork>>,
    caller_private_key: &PrivateKey<CurrentNetwork>,
    delegator_address: &Address<CurrentNetwork>,
    rng: &mut TestRng,
) -> Result<()> {
    execute_function(
        process,
        finalize_store,
        caller_private_key,
        "unbond_delegator_as_validator",
        &[delegator_address.to_string()],
        None,
        rng,
    )
}

/// Perform a `claim_unbond_public`.
fn claim_unbond_public(
    process: &Process<CurrentNetwork>,
    finalize_store: &FinalizeStore<CurrentNetwork, FinalizeMemory<CurrentNetwork>>,
    caller_private_key: &PrivateKey<CurrentNetwork>,
    block_height: u32,
    rng: &mut TestRng,
) -> Result<()> {
    execute_function(process, finalize_store, caller_private_key, "claim_unbond_public", &[], Some(block_height), rng)
}

macro_rules! test_atomic_finalize {
    ($store:ident, $mode:expr, $test:block) => {{
        // The test closure.
        let mut run = || -> Result<()> { atomic_finalize!($store, $mode, $test) };
        // Run the test.
        run()
    }};
}

#[test]
fn test_bond_validator_simple() {
    let rng = &mut TestRng::default();

    // Construct the process.
    let process = Process::<CurrentNetwork>::load().unwrap();
    // Initialize a new finalize store.
    let store = FinalizeStore::<CurrentNetwork, FinalizeMemory<_>>::open(None).unwrap();

    // Initialize the validators.
    let (validators, _) = initialize_stakers(&store, 1, 0, rng).unwrap();
    let (validator_private_key, (validator_address, _)) = validators.first().unwrap();

    // Retrieve the account balance.
    let public_balance = account_balance(&store, validator_address).unwrap();

    // Prepare the validator amount.
    let amount = MIN_VALIDATOR_STAKE;

    // Sanity check the state before finalizing.
    assert_eq!(committee_state(&store, validator_address).unwrap(), None);
    assert_eq!(bond_state(&store, validator_address).unwrap(), None);
    assert_eq!(unbond_state(&store, validator_address).unwrap(), None);
    assert_eq!(account_balance(&store, validator_address).unwrap(), public_balance);

    /* Ensure bonding as a validator with the exact MIN_VALIDATOR_STAKE succeeds. */
    test_atomic_finalize!(store, FinalizeMode::RealRun, {
        // Perform the bond.
        bond_public(&process, &store, validator_private_key, validator_address, amount, rng).unwrap();

        // Check that the committee, bond, and unbond state are correct.
        assert_eq!(committee_state(&store, validator_address).unwrap(), Some((amount, true)));
        assert_eq!(bond_state(&store, validator_address).unwrap(), Some((*validator_address, amount)));
        assert_eq!(unbond_state(&store, validator_address).unwrap(), None);

        // Check that the account balance is correct.
        assert_eq!(account_balance(&store, validator_address).unwrap(), public_balance - amount);
        Ok(())
    })
    .unwrap();

    // Sanity check the state after finalizing.
    assert_eq!(committee_state(&store, validator_address).unwrap(), Some((amount, true)));
    assert_eq!(bond_state(&store, validator_address).unwrap(), Some((*validator_address, amount)));
    assert_eq!(unbond_state(&store, validator_address).unwrap(), None);
    assert_eq!(account_balance(&store, validator_address).unwrap(), public_balance - amount);
}

#[test]
fn test_bond_validator_below_min_stake_fails() {
    let rng = &mut TestRng::default();

    // Construct the process.
    let process = Process::<CurrentNetwork>::load().unwrap();
    // Initialize a new finalize store.
    let store = FinalizeStore::<CurrentNetwork, FinalizeMemory<_>>::open(None).unwrap();

    // Initialize the validators.
    let (validators, _) = initialize_stakers(&store, 1, 0, rng).unwrap();
    let (validator_private_key, (validator_address, _)) = validators.first().unwrap();

    // Retrieve the account balance.
    let public_balance = account_balance(&store, validator_address).unwrap();

    /* Ensure bonding as a validator below the MIN_VALIDATOR_STAKE fails. */
    test_atomic_finalize!(store, FinalizeMode::RealRun, {
        let amount = rng.gen_range(1_000_000..MIN_VALIDATOR_STAKE);
        let result = bond_public(&process, &store, validator_private_key, validator_address, amount, rng);
        assert!(result.is_err());

        // Check that the committee, bond, and unbond state are correct.
        assert_eq!(committee_state(&store, validator_address).unwrap(), None);
        assert_eq!(bond_state(&store, validator_address).unwrap(), None);
        assert_eq!(unbond_state(&store, validator_address).unwrap(), None);

        // Check that the account balance is correct.
        assert_eq!(account_balance(&store, validator_address).unwrap(), public_balance);
        Ok(())
    })
    .unwrap();
}

#[test]
fn test_bond_validator_with_insufficient_funds_fails() {
    let rng = &mut TestRng::default();

    // Construct the process.
    let process = Process::<CurrentNetwork>::load().unwrap();
    // Initialize a new finalize store.
    let store = FinalizeStore::<CurrentNetwork, FinalizeMemory<_>>::open(None).unwrap();

    // Initialize the validators.
    let (validators, _) = initialize_stakers(&store, 1, 0, rng).unwrap();
    let (validator_private_key, (validator_address, _)) = validators.first().unwrap();

    // Retrieve the account balance.
    let public_balance = account_balance(&store, validator_address).unwrap();

    /* Ensure bonding an amount larger than the account balance will fail. */
    test_atomic_finalize!(store, FinalizeMode::RealRun, {
        let amount = public_balance + 1;
        let result = bond_public(&process, &store, validator_private_key, validator_address, amount, rng);
        assert!(result.is_err());

        // Check that the committee, bond, and unbond state are correct.
        assert_eq!(committee_state(&store, validator_address).unwrap(), None);
        assert_eq!(bond_state(&store, validator_address).unwrap(), None);
        assert_eq!(unbond_state(&store, validator_address).unwrap(), None);

        // Check that the account balance is correct.
        assert_eq!(account_balance(&store, validator_address).unwrap(), public_balance);
        Ok(())
    })
    .unwrap();
}

#[test]
fn test_bond_validator_multiple_bonds() {
    let rng = &mut TestRng::default();

    // Construct the process.
    let process = Process::<CurrentNetwork>::load().unwrap();
    // Initialize a new finalize store.
    let store = FinalizeStore::<CurrentNetwork, FinalizeMemory<_>>::open(None).unwrap();

    // Initialize the validators.
    let (validators, _) = initialize_stakers(&store, 1, 0, rng).unwrap();
    let (validator_private_key, (validator_address, _)) = validators.first().unwrap();

    // Retrieve the account balance.
    let public_balance = account_balance(&store, validator_address).unwrap();

    /*  Ensure that bonding additional stake succeeds. */
    test_atomic_finalize!(store, FinalizeMode::RealRun, {
        /* First Bond */

        // Perform the first bond.
        let amount = 1_000_000_000_000u64;
        assert!(amount < public_balance);
        bond_public(&process, &store, validator_private_key, validator_address, amount, rng).unwrap();

        // Check that the committee, bond, and unbond state are correct.
        assert_eq!(committee_state(&store, validator_address).unwrap(), Some((amount, true)));
        assert_eq!(bond_state(&store, validator_address).unwrap(), Some((*validator_address, amount)));
        assert_eq!(unbond_state(&store, validator_address).unwrap(), None);

        // Retrieve the account balance.
        let public_balance_1 = account_balance(&store, validator_address).unwrap();
        assert_eq!(public_balance_1, public_balance - amount);

        /* Second Bond */

        // Perform the second bond.
        let amount = 1_000_000_000_000u64;
        assert!(amount < public_balance_1);
        bond_public(&process, &store, validator_private_key, validator_address, amount, rng).unwrap();

        // Check that the committee, bond, and unbond state are correct.
        assert_eq!(committee_state(&store, validator_address).unwrap(), Some((amount * 2, true)));
        assert_eq!(bond_state(&store, validator_address).unwrap(), Some((*validator_address, amount * 2)));
        assert_eq!(unbond_state(&store, validator_address).unwrap(), None);

        // Retrieve the account balance.
        let public_balance_2 = account_balance(&store, validator_address).unwrap();
        assert_eq!(public_balance_2, public_balance_1 - amount);
        Ok(())
    })
    .unwrap();
}

#[test]
fn test_bond_validator_to_other_validator_fails() {
    let rng = &mut TestRng::default();

    // Construct the process.
    let process = Process::<CurrentNetwork>::load().unwrap();
    // Initialize a new finalize store.
    let store = FinalizeStore::<CurrentNetwork, FinalizeMemory<_>>::open(None).unwrap();

    // Initialize the validators.
    let (validators, _) = initialize_stakers(&store, 2, 0, rng).unwrap();
    let mut validators = validators.into_iter();
    let (validator_private_key_1, (validator_address_1, _)) = validators.next().unwrap();
    let (validator_private_key_2, (validator_address_2, _)) = validators.next().unwrap();

    /* Ensure that bonding to another validator fails. */
    test_atomic_finalize!(store, FinalizeMode::RealRun, {
        /* Validator 1 */

        // Retrieve the account balance.
        let public_balance_1 = account_balance(&store, &validator_address_1).unwrap();
        let public_balance_2 = account_balance(&store, &validator_address_2).unwrap();

        // Perform the bond for validator 1.
        let amount = MIN_VALIDATOR_STAKE;
        bond_public(&process, &store, &validator_private_key_1, &validator_address_1, amount, rng).unwrap();

        // Check that the committee, bond, and unbond state are correct.
        assert_eq!(committee_state(&store, &validator_address_1).unwrap(), Some((amount, true)));
        assert_eq!(committee_state(&store, &validator_address_2).unwrap(), None);
        assert_eq!(bond_state(&store, &validator_address_1).unwrap(), Some((validator_address_1, amount)));
        assert_eq!(bond_state(&store, &validator_address_2).unwrap(), None);
        assert_eq!(unbond_state(&store, &validator_address_1).unwrap(), None);
        assert_eq!(unbond_state(&store, &validator_address_2).unwrap(), None);

        // Retrieve the account balance.
        assert_eq!(account_balance(&store, &validator_address_1).unwrap(), public_balance_1 - amount);
        assert_eq!(account_balance(&store, &validator_address_2).unwrap(), public_balance_2);

        /* Validator 2 */

        // Perform the bond for validator 2.
        let amount = MIN_VALIDATOR_STAKE;
        bond_public(&process, &store, &validator_private_key_2, &validator_address_2, amount, rng).unwrap();

        // Check that the committee, bond, and unbond state are correct.
        assert_eq!(committee_state(&store, &validator_address_1).unwrap(), Some((amount, true)));
        assert_eq!(committee_state(&store, &validator_address_2).unwrap(), Some((amount, true)));
        assert_eq!(bond_state(&store, &validator_address_1).unwrap(), Some((validator_address_1, amount)));
        assert_eq!(bond_state(&store, &validator_address_2).unwrap(), Some((validator_address_2, amount)));
        assert_eq!(unbond_state(&store, &validator_address_1).unwrap(), None);
        assert_eq!(unbond_state(&store, &validator_address_2).unwrap(), None);

        // Retrieve the account balance.
        assert_eq!(account_balance(&store, &validator_address_1).unwrap(), public_balance_1 - amount);
        assert_eq!(account_balance(&store, &validator_address_2).unwrap(), public_balance_2 - amount);

        /* Bond Validator 1 to Validator 2 */

        // Ensure that bonding to another validator fails.
        assert!(public_balance_1 > 2 * amount, "There is not enough balance to bond to another validator.");
        let result = bond_public(&process, &store, &validator_private_key_1, &validator_address_2, amount, rng);
        assert!(result.is_err());
        Ok(())
    })
    .unwrap();
}

#[test]
fn test_bond_delegator_simple() {
    let rng = &mut TestRng::default();

    // Construct the process.
    let process = Process::<CurrentNetwork>::load().unwrap();
    // Initialize a new finalize store.
    let store = FinalizeStore::<CurrentNetwork, FinalizeMemory<_>>::open(None).unwrap();

    // Initialize the validators and delegators.
    let (validators, delegators) = initialize_stakers(&store, 1, 1, rng).unwrap();
    let (validator_private_key, (validator_address, _)) = validators.first().unwrap();
    let (delegator_private_key, (delegator_address, _)) = delegators.first().unwrap();

    // Retrieve the account balances.
    let validator_balance = account_balance(&store, validator_address).unwrap();
    let delegator_balance = account_balance(&store, delegator_address).unwrap();

    // Bond the validator.
    let validator_amount = MIN_VALIDATOR_STAKE;
    bond_public(&process, &store, validator_private_key, validator_address, validator_amount, rng).unwrap();

    // Prepare the delegator amount.
    let delegator_amount = MIN_DELEGATOR_STAKE;

    /* Ensure bonding a delegator with the exact MIN_DELEGATOR_STAKE succeeds. */
    test_atomic_finalize!(store, FinalizeMode::RealRun, {
        // Bond the delegator.
        bond_public(&process, &store, delegator_private_key, validator_address, delegator_amount, rng).unwrap();

        // Check that the committee, bond, and unbond state are correct.
        let combined_amount = validator_amount + delegator_amount;
        assert_eq!(committee_state(&store, validator_address).unwrap(), Some((combined_amount, true)));
        assert_eq!(committee_state(&store, delegator_address).unwrap(), None);
        assert_eq!(bond_state(&store, validator_address).unwrap(), Some((*validator_address, validator_amount)));
        assert_eq!(bond_state(&store, delegator_address).unwrap(), Some((*validator_address, delegator_amount)));
        assert_eq!(unbond_state(&store, validator_address).unwrap(), None);
        assert_eq!(unbond_state(&store, delegator_address).unwrap(), None);

        // Check that the balances are correct.
        assert_eq!(account_balance(&store, validator_address).unwrap(), validator_balance - validator_amount);
        assert_eq!(account_balance(&store, delegator_address).unwrap(), delegator_balance - delegator_amount);
        Ok(())
    })
    .unwrap();

    // Sanity check the state after finalizing.
    assert_eq!(account_balance(&store, delegator_address).unwrap(), delegator_balance - delegator_amount);
}

#[test]
fn test_bond_delegator_below_min_stake_fails() {
    let rng = &mut TestRng::default();

    // Construct the process.
    let process = Process::<CurrentNetwork>::load().unwrap();
    // Initialize a new finalize store.
    let store = FinalizeStore::<CurrentNetwork, FinalizeMemory<_>>::open(None).unwrap();

    // Initialize the validators and delegators.
    let (validators, delegators) = initialize_stakers(&store, 1, 1, rng).unwrap();
    let (validator_private_key, (validator_address, _)) = validators.first().unwrap();
    let (delegator_private_key, (delegator_address, _)) = delegators.first().unwrap();

    // Retrieve the account balance.
    let validator_balance = account_balance(&store, validator_address).unwrap();
    let delegator_balance = account_balance(&store, delegator_address).unwrap();

    /* Ensure bonding as a delegator below the MIN_DELEGATOR_STAKE fails. */
    test_atomic_finalize!(store, FinalizeMode::RealRun, {
        // Bond the validator.
        let validator_amount = MIN_VALIDATOR_STAKE;
        bond_public(&process, &store, validator_private_key, validator_address, validator_amount, rng).unwrap();

        // Bond the delegator.
        let delegator_amount = rng.gen_range(1_000_000..MIN_DELEGATOR_STAKE);
        let result = bond_public(&process, &store, delegator_private_key, validator_address, delegator_amount, rng);
        assert!(result.is_err());

        // Check that the committee, bond, and unbond state are correct.
        assert_eq!(committee_state(&store, validator_address).unwrap(), Some((validator_amount, true)));
        assert_eq!(committee_state(&store, delegator_address).unwrap(), None);
        assert_eq!(bond_state(&store, validator_address).unwrap(), Some((*validator_address, validator_amount)));
        assert_eq!(bond_state(&store, delegator_address).unwrap(), None);
        assert_eq!(unbond_state(&store, validator_address).unwrap(), None);
        assert_eq!(unbond_state(&store, delegator_address).unwrap(), None);

        // Check that the account balance is correct.
        assert_eq!(account_balance(&store, validator_address).unwrap(), validator_balance - validator_amount);
        assert_eq!(account_balance(&store, delegator_address).unwrap(), delegator_balance);
        Ok(())
    })
    .unwrap();
}

#[test]
fn test_bond_delegator_with_insufficient_funds_fails() {
    let rng = &mut TestRng::default();

    // Construct the process.
    let process = Process::<CurrentNetwork>::load().unwrap();
    // Initialize a new finalize store.
    let store = FinalizeStore::<CurrentNetwork, FinalizeMemory<_>>::open(None).unwrap();

    // Initialize the validators and delegators.
    let (validators, delegators) = initialize_stakers(&store, 1, 1, rng).unwrap();
    let (validator_private_key, (validator_address, _)) = validators.first().unwrap();
    let (delegator_private_key, (delegator_address, _)) = delegators.first().unwrap();

    // Retrieve the account balance.
    let validator_balance = account_balance(&store, validator_address).unwrap();
    let delegator_balance = account_balance(&store, delegator_address).unwrap();

    /* Ensure bonding an amount larger than the account balance will fail. */
    test_atomic_finalize!(store, FinalizeMode::RealRun, {
        // Bond the validator.
        let validator_amount = MIN_VALIDATOR_STAKE;
        bond_public(&process, &store, validator_private_key, validator_address, validator_amount, rng).unwrap();

        // Bond the delegator.
        let delegator_amount = delegator_balance + 1;
        let result = bond_public(&process, &store, delegator_private_key, validator_address, delegator_amount, rng);
        assert!(result.is_err());

        // Check that the committee, bond, and unbond state are correct.
        assert_eq!(committee_state(&store, validator_address).unwrap(), Some((validator_amount, true)));
        assert_eq!(committee_state(&store, delegator_address).unwrap(), None);
        assert_eq!(bond_state(&store, validator_address).unwrap(), Some((*validator_address, validator_amount)));
        assert_eq!(bond_state(&store, delegator_address).unwrap(), None);
        assert_eq!(unbond_state(&store, validator_address).unwrap(), None);
        assert_eq!(unbond_state(&store, delegator_address).unwrap(), None);

        // Check that the account balance is correct.
        assert_eq!(account_balance(&store, validator_address).unwrap(), validator_balance - validator_amount);
        assert_eq!(account_balance(&store, delegator_address).unwrap(), delegator_balance);
        Ok(())
    })
    .unwrap();
}

#[test]
fn test_bond_delegator_multiple_bonds() {
    let rng = &mut TestRng::default();

    // Construct the process.
    let process = Process::<CurrentNetwork>::load().unwrap();
    // Initialize a new finalize store.
    let store = FinalizeStore::<CurrentNetwork, FinalizeMemory<_>>::open(None).unwrap();

    // Initialize the validators and delegators.
    let (validators, delegators) = initialize_stakers(&store, 1, 1, rng).unwrap();
    let (validator_private_key, (validator_address, _)) = validators.first().unwrap();
    let (delegator_private_key, (delegator_address, _)) = delegators.first().unwrap();

    // Retrieve the account balance.
    let validator_balance = account_balance(&store, validator_address).unwrap();
    let delegator_balance = account_balance(&store, delegator_address).unwrap();

    // Bond the validator.
    let validator_amount = MIN_VALIDATOR_STAKE;
    bond_public(&process, &store, validator_private_key, validator_address, validator_amount, rng).unwrap();

    /*  Ensure that bonding additional stake as a delegator succeeds. */
    test_atomic_finalize!(store, FinalizeMode::RealRun, {
        /* First Bond */

        // Perform the first bond.
        let delegator_amount = MIN_DELEGATOR_STAKE;
        assert!(delegator_amount < delegator_balance);
        bond_public(&process, &store, delegator_private_key, validator_address, delegator_amount, rng).unwrap();

        // Check that the committee, bond, and unbond state are correct.
        let combined_amount = validator_amount + delegator_amount;
        assert_eq!(committee_state(&store, validator_address).unwrap(), Some((combined_amount, true)));
        assert_eq!(committee_state(&store, delegator_address).unwrap(), None);
        assert_eq!(bond_state(&store, validator_address).unwrap(), Some((*validator_address, validator_amount)));
        assert_eq!(bond_state(&store, delegator_address).unwrap(), Some((*validator_address, delegator_amount)));
        assert_eq!(unbond_state(&store, validator_address).unwrap(), None);
        assert_eq!(unbond_state(&store, delegator_address).unwrap(), None);

        // Retrieve the account balance.
        let validator_balance_1 = account_balance(&store, validator_address).unwrap();
        let delegator_balance_1 = account_balance(&store, delegator_address).unwrap();
        assert_eq!(validator_balance_1, validator_balance - validator_amount);
        assert_eq!(delegator_balance_1, delegator_balance - delegator_amount);

        /* Second Bond */

        // Perform the second bond.
        let delegator_amount = MIN_DELEGATOR_STAKE;
        assert!(delegator_amount < delegator_balance_1);
        bond_public(&process, &store, delegator_private_key, validator_address, delegator_amount, rng).unwrap();

        // Check that the committee, bond, and unbond state are correct.
        let combined_amount = validator_amount + delegator_amount + delegator_amount;
        assert_eq!(committee_state(&store, validator_address).unwrap(), Some((combined_amount, true)));
        assert_eq!(committee_state(&store, delegator_address).unwrap(), None);
        assert_eq!(bond_state(&store, validator_address).unwrap(), Some((*validator_address, validator_amount)));
        assert_eq!(bond_state(&store, delegator_address).unwrap(), Some((*validator_address, 2 * delegator_amount)));
        assert_eq!(unbond_state(&store, validator_address).unwrap(), None);
        assert_eq!(unbond_state(&store, delegator_address).unwrap(), None);

        // Retrieve the account balance.
        let validator_balance_2 = account_balance(&store, validator_address).unwrap();
        let delegator_balance_2 = account_balance(&store, delegator_address).unwrap();
        assert_eq!(validator_balance_2, validator_balance_1);
        assert_eq!(delegator_balance_2, delegator_balance_1 - delegator_amount);
        Ok(())
    })
    .unwrap();
}

#[test]
fn test_bond_delegator_to_nonexistent_validator_fails() {
    let rng = &mut TestRng::default();

    // Construct the process.
    let process = Process::<CurrentNetwork>::load().unwrap();
    // Initialize a new finalize store.
    let store = FinalizeStore::<CurrentNetwork, FinalizeMemory<_>>::open(None).unwrap();

    // Initialize the validators and delegators.
    let (_, delegators) = initialize_stakers(&store, 0, 1, rng).unwrap();
    let (delegator_private_key, (delegator_address, _)) = delegators.first().unwrap();

    // Sample a random validator address.
    let validator_address = &Address::new(rng.gen());

    // Retrieve the account balance.
    let public_balance = account_balance(&store, delegator_address).unwrap();
    assert!(public_balance > MIN_DELEGATOR_STAKE);

    /* Ensure bonding to a nonexistent validator fails. */
    test_atomic_finalize!(store, FinalizeMode::RealRun, {
        let amount = MIN_DELEGATOR_STAKE;
        let result = bond_public(&process, &store, delegator_private_key, validator_address, amount, rng);
        assert!(result.is_err());
        assert_eq!(committee_state(&store, validator_address).unwrap(), None);
        assert_eq!(committee_state(&store, delegator_address).unwrap(), None);
        assert_eq!(bond_state(&store, validator_address).unwrap(), None);
        assert_eq!(bond_state(&store, delegator_address).unwrap(), None);
        assert_eq!(unbond_state(&store, validator_address).unwrap(), None);
        assert_eq!(unbond_state(&store, delegator_address).unwrap(), None);
        assert_eq!(account_balance(&store, delegator_address).unwrap(), public_balance);
        Ok(())
    })
    .unwrap();

    // Sanity check after finalizing.
    assert_eq!(account_balance(&store, delegator_address).unwrap(), public_balance);
}

#[test]
fn test_bond_delegator_to_non_validator_fails() {
    let rng = &mut TestRng::default();

    // Construct the process.
    let process = Process::<CurrentNetwork>::load().unwrap();

    // Initialize a new finalize store.
    let finalize_store = FinalizeStore::<CurrentNetwork, FinalizeMemory<_>>::open(None).unwrap();

    // Initialize the validators and delegators.
    let (_, delegators) = initialize_stakers(&finalize_store, 0, 1, rng).unwrap();
    let (delegator_private_key, (_, _)) = delegators.first().unwrap();

    /* Ensure bonding a new delegator to a non-existent validator fails. */

    // Generate a random address.
    let non_validator_private_key = PrivateKey::new(rng).unwrap();
    let non_validator_address = Address::try_from(&non_validator_private_key).unwrap();

    // Bond the delegator.
    let delegator_amount = 1_000_000u64;
    assert!(
        bond_public(&process, &finalize_store, delegator_private_key, &non_validator_address, delegator_amount, rng)
            .is_err()
    );
}

#[test]
fn test_bond_delegator_to_multiple_validators_fails() {
    let rng = &mut TestRng::default();

    // Construct the process.
    let process = Process::<CurrentNetwork>::load().unwrap();

    // Initialize a new finalize store.
    let finalize_store = FinalizeStore::<CurrentNetwork, FinalizeMemory<_>>::open(None).unwrap();

    // Initialize the validators and delegators.
    let (validators, delegators) = initialize_stakers(&finalize_store, 2, 1, rng).unwrap();
    let mut validators = validators.into_iter();
    let (validator_private_key_1, (validator_address_1, _)) = validators.next().unwrap();
    let (validator_private_key_2, (validator_address_2, _)) = validators.next().unwrap();
    let (delegator_private_key, (_, _)) = delegators.first().unwrap();

    /* Ensure bonding a delegator to a multiple validators fails. */

    // Perform the bond for validator 1.
    let amount = 1_000_000_000_000u64;
    bond_public(&process, &finalize_store, &validator_private_key_1, &validator_address_1, amount, rng).unwrap();

    // Perform the bond for validator 2.
    bond_public(&process, &finalize_store, &validator_private_key_2, &validator_address_2, amount, rng).unwrap();

    // Bond the delegator to validator 1.
    let delegator_amount = 1_000_000u64;
    bond_public(&process, &finalize_store, delegator_private_key, &validator_address_1, delegator_amount, rng).unwrap();

    // Bonding the delegator to validator 2 should fail.
    let delegator_amount = 1_000_000u64;
    assert!(
        bond_public(&process, &finalize_store, delegator_private_key, &validator_address_2, delegator_amount, rng)
            .is_err()
    );
}

#[test]
fn test_unbond_validator() {
    let rng = &mut TestRng::default();

    // Construct the process.
    let process = Process::<CurrentNetwork>::load().unwrap();

    // Initialize a new finalize store.
    let finalize_store = FinalizeStore::<CurrentNetwork, FinalizeMemory<_>>::open(None).unwrap();

    // Initialize the validators and delegators.
    let (validators, _) = initialize_stakers(&finalize_store, 1, 0, rng).unwrap();
    let (validator_private_key, (validator_address, _)) = validators.first().unwrap();

    // Perform the bond.
    let validator_amount = 5_000_000_000_000u64;
    bond_public(&process, &finalize_store, validator_private_key, validator_address, validator_amount, rng).unwrap();

    /* Ensure that the validator can unbond if the remaining balance is more than 1M credits. */

    let unbond_amount_1 = rng.gen_range(1_000_000..validator_amount - 1_000_000);
    let block_height_1 = rng.gen_range(1..100);
    unbond_public(&process, &finalize_store, validator_private_key, unbond_amount_1, block_height_1, rng).unwrap();

    assert_eq!(
        committee_state(&finalize_store, validator_address).unwrap(),
        Some((validator_amount - unbond_amount_1, true))
    );
    assert_eq!(
        bond_state(&finalize_store, validator_address).unwrap(),
        Some((*validator_address, validator_amount - unbond_amount_1))
    );
    assert_eq!(
        unbond_state(&finalize_store, validator_address).unwrap(),
        Some((unbond_amount_1, block_height_1 + NUM_BLOCKS_TO_UNLOCK))
    );

    /* Ensure that the validator can unbond its entire stake if there are no delegators. */

    let unbond_amount_2 = validator_amount - unbond_amount_1;
    let block_height_2 = rng.gen_range(block_height_1..1000);
    unbond_public(&process, &finalize_store, validator_private_key, unbond_amount_2, block_height_2, rng).unwrap();

    assert_eq!(committee_state(&finalize_store, validator_address).unwrap(), None);
    assert_eq!(bond_state(&finalize_store, validator_address).unwrap(), None);
    assert_eq!(
        unbond_state(&finalize_store, validator_address).unwrap(),
        Some((validator_amount, block_height_2 + NUM_BLOCKS_TO_UNLOCK))
    );
}

#[test]
fn test_unbond_validator_under_minimum_stake_removes() {
    let rng = &mut TestRng::default();

    // Construct the process.
    let process = Process::<CurrentNetwork>::load().unwrap();

    // Initialize a new finalize store.
    let finalize_store = FinalizeStore::<CurrentNetwork, FinalizeMemory<_>>::open(None).unwrap();

    // Initialize the validators and delegators.
    let (validators, _) = initialize_stakers(&finalize_store, 1, 0, rng).unwrap();
    let (validator_private_key, (validator_address, _)) = validators.first().unwrap();

    // Bond the validator.
    let validator_amount = 5_000_000_000_000u64;
    bond_public(&process, &finalize_store, validator_private_key, validator_address, validator_amount, rng).unwrap();

    /* Ensure that the validator will be removed if the remaining balance is less than 1M credits. */

    let unbond_amount = rng.gen_range(validator_amount - (MIN_VALIDATOR_STAKE - 1)..validator_amount);
    let block_height = rng.gen_range(1..100);
    unbond_public(&process, &finalize_store, validator_private_key, unbond_amount, block_height, rng).unwrap();

    assert_eq!(committee_state(&finalize_store, validator_address).unwrap(), None);
    assert_eq!(bond_state(&finalize_store, validator_address).unwrap(), None);
    assert_eq!(
        unbond_state(&finalize_store, validator_address).unwrap(),
        Some((validator_amount, block_height + NUM_BLOCKS_TO_UNLOCK))
    );
}

#[test]
fn test_unbond_validator_failed() {
    let rng = &mut TestRng::default();

    // Construct the process.
    let process = Process::<CurrentNetwork>::load().unwrap();

    // Initialize a new finalize store.
    let finalize_store = FinalizeStore::<CurrentNetwork, FinalizeMemory<_>>::open(None).unwrap();

    // Initialize the validators and delegators.
    let (validators, delegators) = initialize_stakers(&finalize_store, 1, 1, rng).unwrap();
    let (validator_private_key, (validator_address, _)) = validators.first().unwrap();
    let (delegator_private_key, (_, _)) = delegators.first().unwrap();

    // Bond the validator.
    let validator_amount = 5_000_000_000_000u64;
    bond_public(&process, &finalize_store, validator_private_key, validator_address, validator_amount, rng).unwrap();

    // Bond the delegator.
    let delegator_amount = MIN_DELEGATOR_STAKE;
    bond_public(&process, &finalize_store, delegator_private_key, validator_address, delegator_amount, rng).unwrap();

    /* Ensure that the validator can't unbond more than its stake */

    assert!(unbond_public(&process, &finalize_store, validator_private_key, validator_amount + 1, 1, rng).is_err());

    /* Ensure that the validator can't unbond entire stake if there are delegators. */

    assert!(unbond_public(&process, &finalize_store, validator_private_key, validator_amount, 1, rng).is_err());
}

#[test]
fn test_unbond_delegator() {
    let rng = &mut TestRng::default();

    // Construct the process.
    let process = Process::<CurrentNetwork>::load().unwrap();

    // Initialize a new finalize store.
    let finalize_store = FinalizeStore::<CurrentNetwork, FinalizeMemory<_>>::open(None).unwrap();

    // Initialize the validators and delegators.
    let (validators, delegators) = initialize_stakers(&finalize_store, 1, 1, rng).unwrap();
    let (validator_private_key, (validator_address, _)) = validators.first().unwrap();
    let (delegator_private_key, (delegator_address, _)) = delegators.first().unwrap();

    // Bond the validator.
    let validator_amount = 5_000_000_000_000u64;
    bond_public(&process, &finalize_store, validator_private_key, validator_address, validator_amount, rng).unwrap();

    // Bond the delegator.
    let delegator_amount = 20_000_000u64;
    bond_public(&process, &finalize_store, delegator_private_key, validator_address, delegator_amount, rng).unwrap();

    /* Ensure that the delegator can unbond if the remaining balance is more than 10 credits. */

    let unbond_amount_1 = rng.gen_range(1_000_000..delegator_amount - MIN_DELEGATOR_STAKE);
    let block_height_1 = rng.gen_range(1..100);
    unbond_public(&process, &finalize_store, delegator_private_key, unbond_amount_1, block_height_1, rng).unwrap();

    assert_eq!(
        bond_state(&finalize_store, delegator_address).unwrap(),
        Some((*validator_address, delegator_amount - unbond_amount_1))
    );
    assert_eq!(
        unbond_state(&finalize_store, delegator_address).unwrap(),
        Some((unbond_amount_1, block_height_1 + NUM_BLOCKS_TO_UNLOCK))
    );

    /* Ensure that the delegator can unbond its entire stake. */

    let unbond_amount_2 = delegator_amount - unbond_amount_1;
    let block_height_2 = rng.gen_range(block_height_1..1000);
    unbond_public(&process, &finalize_store, delegator_private_key, unbond_amount_2, block_height_2, rng).unwrap();

    assert_eq!(bond_state(&finalize_store, delegator_address).unwrap(), None);
    assert_eq!(
        unbond_state(&finalize_store, delegator_address).unwrap(),
        Some((delegator_amount, block_height_2 + NUM_BLOCKS_TO_UNLOCK))
    );
}

#[test]
fn test_unbond_delegator_under_minimum_stake_removes() {
    let rng = &mut TestRng::default();

    // Construct the process.
    let process = Process::<CurrentNetwork>::load().unwrap();

    // Initialize a new finalize store.
    let finalize_store = FinalizeStore::<CurrentNetwork, FinalizeMemory<_>>::open(None).unwrap();

    // Initialize the validators and delegators.
    let (validators, delegators) = initialize_stakers(&finalize_store, 1, 1, rng).unwrap();
    let (validator_private_key, (validator_address, _)) = validators.first().unwrap();
    let (delegator_private_key, (delegator_address, _)) = delegators.first().unwrap();

    // Bond the validator.
    let validator_amount = 5_000_000_000_000u64;
    bond_public(&process, &finalize_store, validator_private_key, validator_address, validator_amount, rng).unwrap();

    // Bond the delegator.
    let delegator_amount = 20_000_000u64;
    bond_public(&process, &finalize_store, delegator_private_key, validator_address, delegator_amount, rng).unwrap();

    /* Ensure that the delegator will be removed if the remaining balance is less than 10 credits. */

    let unbond_amount = rng.gen_range(delegator_amount - (MIN_DELEGATOR_STAKE - 1)..delegator_amount);
    let block_height = rng.gen_range(1..100);
    unbond_public(&process, &finalize_store, delegator_private_key, unbond_amount, block_height, rng).unwrap();

    assert_eq!(bond_state(&finalize_store, delegator_address).unwrap(), None);
    assert_eq!(
        unbond_state(&finalize_store, delegator_address).unwrap(),
        Some((delegator_amount, block_height + NUM_BLOCKS_TO_UNLOCK))
    );
}

#[test]
fn test_unbond_delegator_fails() {
    let rng = &mut TestRng::default();

    // Construct the process.
    let process = Process::<CurrentNetwork>::load().unwrap();

    // Initialize a new finalize store.
    let finalize_store = FinalizeStore::<CurrentNetwork, FinalizeMemory<_>>::open(None).unwrap();

    // Initialize the validators and delegators.
    let (validators, delegators) = initialize_stakers(&finalize_store, 1, 1, rng).unwrap();
    let (validator_private_key, (validator_address, _)) = validators.first().unwrap();
    let (delegator_private_key, (_, _)) = delegators.first().unwrap();

    // Bond the validator.
    let validator_amount = 5_000_000_000_000u64;
    bond_public(&process, &finalize_store, validator_private_key, validator_address, validator_amount, rng).unwrap();

    // Bond the delegator.
    let delegator_amount = 20_000_000u64;
    bond_public(&process, &finalize_store, delegator_private_key, validator_address, delegator_amount, rng).unwrap();

    /* Ensure that the delegator can't unbond more than its stake */

    assert!(unbond_public(&process, &finalize_store, delegator_private_key, delegator_amount + 1, 1, rng).is_err());
}

#[test]
fn test_unbond_delegator_as_validator() {
    let rng = &mut TestRng::default();

    // Construct the process.
    let process = Process::<CurrentNetwork>::load().unwrap();

    // Initialize a new finalize store.
    let finalize_store = FinalizeStore::<CurrentNetwork, FinalizeMemory<_>>::open(None).unwrap();

    // Initialize the validators and delegators.
    let (validators, delegators) = initialize_stakers(&finalize_store, 2, 1, rng).unwrap();
    let mut validators = validators.into_iter();
    let (validator_private_key_1, (validator_address_1, _)) = validators.next().unwrap();
    let (validator_private_key_2, (validator_address_2, _)) = validators.next().unwrap();
    let (delegator_private_key, (delegator_address, _)) = delegators.first().unwrap();

    /* Ensure unbonding a delegator as an open validator fails. */

    // Bond the validators.
    let validator_amount = 1_000_000_000_000u64;
    bond_public(&process, &finalize_store, &validator_private_key_1, &validator_address_1, validator_amount, rng)
        .unwrap();
    bond_public(&process, &finalize_store, &validator_private_key_2, &validator_address_2, validator_amount, rng)
        .unwrap();

    // Bond the delegator.
    let delegator_amount = 1_000_000u64;
    bond_public(&process, &finalize_store, delegator_private_key, &validator_address_1, delegator_amount, rng).unwrap();

    // Ensure that unbonding a delegator as an open validator fails.
    assert!(
        unbond_delegator_as_validator(&process, &finalize_store, &validator_private_key_1, delegator_address, rng)
            .is_err()
    );

    // Set the validator `is_open` state to `false`.
    set_validator_state(&process, &finalize_store, &validator_private_key_1, false, rng).unwrap();

    /* Ensure unbonding a delegator for another closed validator fails. */

    // Ensure that unbonding a delegator as an open validator fails.
    assert!(
        unbond_delegator_as_validator(&process, &finalize_store, &validator_private_key_2, delegator_address, rng)
            .is_err()
    );

    /* Ensure unbonding a delegator as a closed validator succeeds. */

    // Ensure that unbonding a delegator as a closed validator succeeds.
    unbond_delegator_as_validator(&process, &finalize_store, &validator_private_key_1, delegator_address, rng).unwrap();

    assert_eq!(committee_state(&finalize_store, &validator_address_1).unwrap(), Some((validator_amount, false)));
    assert_eq!(bond_state(&finalize_store, delegator_address).unwrap(), None);
    assert_eq!(unbond_state(&finalize_store, delegator_address).unwrap().unwrap().0, delegator_amount);
}

#[test]
fn test_claim_unbond() {
    let rng = &mut TestRng::default();

    // Construct the process.
    let process = Process::<CurrentNetwork>::load().unwrap();

    // Initialize a new finalize store.
    let finalize_store = FinalizeStore::<CurrentNetwork, FinalizeMemory<_>>::open(None).unwrap();

    // Initialize the validators and delegators.
    let (validators, _) = initialize_stakers(&finalize_store, 1, 0, rng).unwrap();
    let (validator_private_key, (validator_address, _)) = validators.first().unwrap();

    // Fetch the account balance.
    let public_balance = account_balance(&finalize_store, validator_address).unwrap();

    // Perform the bond.
    let validator_amount = 1_000_000_000_000u64;
    bond_public(&process, &finalize_store, validator_private_key, validator_address, validator_amount, rng).unwrap();

    /* Ensure claiming an unbond fails when no unbond_state exists. */

    assert!(claim_unbond_public(&process, &finalize_store, validator_private_key, 1, rng).is_err());

    // Perform the unbond.
    unbond_public(&process, &finalize_store, validator_private_key, validator_amount, 1, rng).unwrap();
    let unbond_height = unbond_state(&finalize_store, validator_address).unwrap().unwrap().1;

    /* Ensure claiming an unbond before the unlock height fails. */

    assert!(claim_unbond_public(&process, &finalize_store, validator_private_key, unbond_height - 1, rng).is_err());

    /* Ensure that claiming an unbond after the unlock height succeeds. */
    claim_unbond_public(&process, &finalize_store, validator_private_key, unbond_height, rng).unwrap();
    assert_eq!(account_balance(&finalize_store, validator_address).unwrap(), public_balance);
}

#[test]
fn test_set_validator_state() {
    let rng = &mut TestRng::default();

    // Construct the process.
    let process = Process::<CurrentNetwork>::load().unwrap();

    // Initialize a new finalize store.
    let finalize_store = FinalizeStore::<CurrentNetwork, FinalizeMemory<_>>::open(None).unwrap();

    // Initialize the validators.
    let (validators, _) = initialize_stakers(&finalize_store, 1, 0, rng).unwrap();
    let (validator_private_key, (validator_address, _)) = validators.first().unwrap();

    /* Ensure calling `set_validator_state` succeeds. */

    // Perform the bond.
    let amount = 1_000_000_000_000u64;
    bond_public(&process, &finalize_store, validator_private_key, validator_address, amount, rng).unwrap();

    // Check that the validator state is correct.
    assert_eq!(committee_state(&finalize_store, validator_address).unwrap(), Some((amount, true)));

    // Set the validator `is_open` state to `false`.
    set_validator_state(&process, &finalize_store, validator_private_key, false, rng).unwrap();
    assert_eq!(committee_state(&finalize_store, validator_address).unwrap(), Some((amount, false)));

    // Set the validator state `is_open` to `false` again.
    set_validator_state(&process, &finalize_store, validator_private_key, false, rng).unwrap();
    assert_eq!(committee_state(&finalize_store, validator_address).unwrap(), Some((amount, false)));

    // Set the validator `is_open` state back to `true`.
    set_validator_state(&process, &finalize_store, validator_private_key, true, rng).unwrap();
    assert_eq!(committee_state(&finalize_store, validator_address).unwrap(), Some((amount, true)));
}

#[test]
fn test_set_validator_state_for_non_validator_fails() {
    let rng = &mut TestRng::default();

    // Construct the process.
    let process = Process::<CurrentNetwork>::load().unwrap();

    // Initialize a new finalize store.
    let finalize_store = FinalizeStore::<CurrentNetwork, FinalizeMemory<_>>::open(None).unwrap();

    /* Ensure calling `set_validator_state` as a non-validator fails. */

    // Initialize a new private key.
    let private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();

    // Set the validator state to `false`.
    assert!(set_validator_state(&process, &finalize_store, &private_key, false, rng).is_err());
}

#[test]
fn test_bonding_to_closed_fails() {
    let rng = &mut TestRng::default();

    // Construct the process.
    let process = Process::<CurrentNetwork>::load().unwrap();

    // Initialize a new finalize store.
    let finalize_store = FinalizeStore::<CurrentNetwork, FinalizeMemory<_>>::open(None).unwrap();

    // Initialize the validators and delegators.
    let (validators, delegators) = initialize_stakers(&finalize_store, 1, 1, rng).unwrap();
    let (validator_private_key, (validator_address, _)) = validators.first().unwrap();
    let (delegator_private_key, (_, _)) = delegators.first().unwrap();

    /* Ensure bonding to a closed validator fails. */

    // Perform the bond.
    let amount = 1_000_000_000_000u64;
    bond_public(&process, &finalize_store, validator_private_key, validator_address, amount, rng).unwrap();

    // Set the validator `is_open` state to `false`.
    set_validator_state(&process, &finalize_store, validator_private_key, false, rng).unwrap();

    // Ensure that the validator can't bond additional stake.
    let validator_amount = 1_000_000_000_000u64;
    assert!(
        bond_public(&process, &finalize_store, validator_private_key, validator_address, validator_amount, rng)
            .is_err()
    );

    // Ensure that delegators can't bond to the validator.
    let delegator_amount = 1_000_000u64;
    assert!(
        bond_public(&process, &finalize_store, delegator_private_key, validator_address, delegator_amount, rng)
            .is_err()
    );
}

// Test cases:

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
