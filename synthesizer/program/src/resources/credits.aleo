// Disclosure: This program is experimental and not intended for production use.
// This program is provided "as is" without warranties of any kind.
// The author disclaims liability for damages of any kind arising from the use of this program.
program credits.aleo;

/**********************************************************************************************************************/

/// The `committee` mapping contains the active validator set and their corresponding stake.
mapping committee:
    // The key represents the address of the validator.
    key validator as address.public;
    // The value represents the state of the validator.
    value state as state.public;

// The `state` struct tracks the state of the validator.
struct state:
    // The amount of microcredits bonded to the validator, by the validator and its delegators.
    microcredits as u64.public;
    // The boolean flag indicating if the validator is locked.
    is_locked as boolean.public;

/**********************************************************************************************************************/

// The `bonded` mapping represents the amount of microcredits that are currently bonded.
mapping bonded:
    // The key represents the address of the staker, which includes the validators and their delegators.
    key staker as address.public;
    // The value represents the bond.
    value bond as bond.public;

// The `bond` struct tracks the amount of microcredits that are currently bonded to the specified validator.
struct bond:
    // The address of the validator.
    validator as address;
    // The amount of microcredits that are currently bonded to the specified validator.
    microcredits as u64;

/**********************************************************************************************************************/

// The `unbonding` mapping contains a set of stakers with their unbonding microcredits and unlock height.
mapping unbonding:
    // The key represents the address of the staker, which includes the validators and their delegators.
    key staker as address.public;
    // The value represents the unbond.
    value unbond as unbond.public;

// The `unbond` struct tracks the microcredits that are currently unbonding.
struct unbond:
    // The amount of microcredits that are currently unbonding.
    microcredits as u64;
    // The block height at which the unbonding will be complete, and can be claimed.
    height as u32;

/**********************************************************************************************************************/

// The `account` mapping is used to store credits publicly.
mapping account:
    // The key represents the address of the owner.
    key owner as address.public;
    // The value represents the amount of public microcredits that belong to the specified owner.
    value microcredits as u64.public;

// The `credits` record is used to store credits privately.
record credits:
    // The address of the owner.
    owner as address.private;
    // The amount of private microcredits that belong to the specified owner.
    microcredits as u64.private;

/**********************************************************************************************************************/

// fn bond_validator
// - if the bond is now 33% or more, lock the validator. (determine how hard to impl this)

// fn unbond_validator
//  - can only be triggered after the validator has unbonded all of their delegators.
//  - does it matter if the validator is locked here?

// Useful for when you want to lock your validator from others bonding more.
// i.e. you as validator want to unbond yourself, or say you're approaching 33% of the total stake.
// fn lock_validator

// Allows you and others to bond more to your validator.
// fn unlock_validator

// Open Questions:
// - Should the 720 be more?

/**********************************************************************************************************************/

function bond_public:
    // Input the validator's address.
    input r0 as address.public;
    // Input the amount of microcredits to bond.
    input r1 as u64.public;

    // Determine if the amount is at least one credit.
    gte r1 1_000_000u64 into r2;
    // Enforce the amount is at least one credit.
    assert.eq r2 true;

    // Bond the specified amount of microcredits to the specified validator.
    finalize self.caller r0 r1;

finalize bond_public:
    // Input the staker's address.
    input r0 as address.public;
    // Input the validator's address.
    input r1 as address.public;
    // Input the amount of microcredits to bond.
    input r2 as u64.public;

    // Determine whether the caller is a validator.
    is.eq r0 r1 into r3;
    // If the caller is a validator, jump to the `bond_validator` logic.
    branch.eq r3 true to bond_validator;
    // If the caller is not a validator, jump to the `bond_delegator` logic.
    branch.eq r3 false to bond_delegator;

    /******* Bond Validator *******/

    // Starts the `bond_validator` logic.
    position bond_validator;

    /* Start Committee */

    // Construct the initial committee state.
    cast 0u64 false into r4 as state;
    // Retrieve the state of the specified validator.
    get.or_use committee[r0] r4 into r5;
    // Ensure that the validator is unlocked.
    assert_eq r5.is_locked false;

    // Increment the stake for the specified validator.
    add r5.microcredits r2 into r6;
    // Determine if the amount is at least one million credits.
    gte r6 1_000_000_000_000u64 into r7;
    // Enforce the amount is at least one million credits.
    assert.eq r7 true;

    // Construct the updated committee state.
    cast r6 r5.is_locked into r8 as state;

    /* End Committee */

    /* Start Bonded */

    // Construct the initial bond struct.
    cast r1 0u64 into r9 as bond;
    // Get the bond struct for the caller, or default to the initial bond struct.
    get.or_use bonded[r0] r9 into r10;
    // Enforce the validator matches in the bond struct.
    assert.eq r10.validator r1;

    // Increment the microcredits in the bond struct.
    add r10.microcredits r2 into r11;
    // Construct the updated bond struct.
    cast r1 r11 into r12 as bond;

    /* End Bonded */

    /* Start Account */

    // Get the balance of the caller.
    // If the account does not exist, this finalize scope will fail.
    get account[r0] into r13;
    // Decrement the balance of the caller.
    sub r13 r2 into r14;

    /* End Account */

    /* Start Writes */

    // Update the state of the specified validator.
    set committee[r0] r8;
    // Update the bond struct for the caller.
    set bonded[r0] r12;
    // Update the balance of the caller.
    set account[r0] r14;

    /* End Writes */

    // Ends the `bond_validator` logic.
    branch.eq true true to end;

    /******* Bond Delegator *******/

    // Starts the `bond_delegator` logic.
    position bond_delegator;

    /* Start Committee */

    // Check if the caller is a validator.
    contains committee[r0] into r15;
    // Enforce the caller is *not* a validator.
    assert.eq r15 false;

    // Get the stake for the specified validator.
    // If the validator does not exist, this finalize scope will fail.
    get committee[r1] into r16;
    // Ensure that the validator is unlocked.
    assert.eq r16.is_locked false;

    // Increment the stake for the specified validator.
    add r16.microcredits r2 into r17;
    // Construct the updated state struct.
    cast r17 r16.is_locked into r18 as state;

    /* End Committee */

    /* Start Bonded */

    // Construct the initial bond struct.
    cast r1 0u64 into r19 as bond;
    // Get the bond struct for the caller, or default to the initial bond struct.
    get.or_use bonded[r0] r19 into r20;
    // Enforce the validator matches in the bond struct.
    assert.eq r20.validator r1;

    // Increment the microcredits in the bond struct.
    add r20.microcredits r2 into r21;
    // Construct the updated bond struct.
    cast r1 r21 into r22 as bond;

    /* End Bonded */

    /* Start Account */

    // Get the balance of the caller.
    // If the account does not exist, this finalize scope will fail.
    get account[r0] into r23;
    // Decrement the balance of the caller.
    sub r23 r2 into r24;

    /* End Account */

    /* Start Writes */

    // Update the stake for the specified validator.
    set r18 into committee[r1];
    // Update the bond struct for the caller.
    set r22 into bonded[r0];
    // Update the balance of the caller.
    set r24 into account[r0];

    /* End Writes */

    // The terminus.
    position end;

/**********************************************************************************************************************/

function lock_validator:
    // Lock the validator.
    finalize self.caller;

finalize lock_validator:
    // Input the validator's address.
    input r0 as address.public;

    // Get the state for the specified validator.
    // If the validator does not exist, this finalize scope will fail.
    get committee[r0] into r1;
    // Ensure that the validator is unlocked.
    assert.eq r1.is_locked false;

    // Construct the updated committee state.
    cast r1.microcredits true into r2 as state;
    // Update the state for the specified validator.
    set committee[r0] r2;

/**********************************************************************************************************************/

function unlock_validator:
    // Unlock the validator.
    finalize self.caller;

finalize unlock_validator:
    // Input the validator's address.
    input r0 as address.public;

    // Get the state for the specified validator.
    // If the validator does not exist, this finalize scope will fail.
    get committee[r0] into r1;
    // Ensure that the validator is locked.
    assert.eq r1.is_locked true;

    // Construct the updated committee state.
    cast r1.microcredits false into r2 as state;
    // Update the state for the specified validator.
    set committee[r0] r2;

/**********************************************************************************************************************/
d_validator:
//    // Input the amount of microcredits to unbond.
//    input r0 as u64.public;
//
//    // Enforce the amount is nonzero.
//    assert.neq r0 0u64;
//
//    // Unbond the specified amount of microcredits to the caller.
//    finalize self.caller r0;
//
//// Check that the caller is currently a validator.
//
//// If the validator is not locked:
//    // Ensure that the remaining stack is greater than 1 million credits.
//
//// If the validator is locked:
//    // Ensure that there are no more delegators (bond amount and state is equivalent)
//
//    // Ensure that input amount is the entire unbonding amount?
//    // Remove the validator from the committee.
//    // Unbond the specified amount of microcredits to the validator.
//finalize unbond_validator:
//    // Input the validator's address.
//    input r0 as address.public;
//    // Input the amount of microcredits to unbond.
//    input r1 as u64.public;
//
//    // Get the state for the specified validator.
//    // If the validator does not exist, this finalize scope will fail.
//    get committee[r3.validator] into r2;
//    // Ensure that the validator is locked.
//    assert.eq r2.is_locked true;
//    // Decrement the stake for the specified validator.
//    sub r2.microcredits r1 into r3;
//
//    // Get the bond struct for the validator, or fail if it does not exist.
//    get bonded[r0] into r4;
//    // Decrement the microcredits in the bond struct.
//    sub r4.microcredits r1 into r5;
//
//    // Determine if the remaining bond is at least one million credits.
//    gte r5 1_000_000_000_000u64 into r6;
//
//    // If the remaining balance is greater than 1 million, jump to the `remain_validator` logic.
//    branch.eq r6 true to remain_validator;
//    // If the remaining balance is less than 1 million, jump to the `remove_validator` logic.
//    branch.eq r6 false to remove_validator;
//
//    /******* Remain Validator *******/
//
//    // Starts the `remain_validator` logic.
//    position remain_validator;
//
//    // Construct the updated state struct.
//    cast r3 r2.is_locked into r7 as state;
//    // Update the state for the validator.
//    set committee[r0] r7;
//
//    // Construct the updated bond struct.
//    cast r4.validator r5 into r8 as bond;
//    // Update the bond struct for the validator.
//    set bonded[r0] r8;
//
//    // Ends the `sufficient_balance` logic.
//    branch.eq true true to end_if;
//
//    /******* Remove Validator *******/
//
//    // Starts the `remove_validator` logic.
//    position remove_validator;
//
//    // Ensure that the validator has no delegators.
//    assert.eq r3 r5;
//    // Ensure that the amount being unbonded is the entire amount.
//    assert.eq r3 0u64;;
//
//    // Remove the validator from the committee.
//    remove committee[r0];
//    // Remove the bond struct for the validator.
//    remove bonded[r0];
//
//    // Ends the `insufficient_balance` logic.
//    branch.eq true true to end_if;
//
//    // The end of the if condition.
//    position end_if;
//
//    /* Start Unbond */
//
//    // Construct the initial unbond struct.
//    cast 0u64 0u32 into r9 as unbond;
//    // Get the unbond struct for the caller, or default to the initial unbond struct.
//    get.or_use unbonding[r0] r9 into r10;
//
//    // Increment the microcredits in the unbond struct.
//    add r10.microcredits r1 into r11;
//    // Compute the height at which the unbonding will be complete, starting from the current block.
//    // Note: Calling unbond across multiple blocks before the unbonding is complete will reset the height each time.
//    add block.height 720u32 into r12;
//
//    // Construct the updated unbond struct.
//    cast r11 r12 into r13 as unbond;
//    // Update the unbond struct for the caller.
//    set unbonding[r0] r13;
//
//    /* End Unbond */
//function unbon

/**********************************************************************************************************************/

function unbond_delegator:
    // Input the amount of microcredits to unbond.
    input r0 as u64.public;

    // Enforce the amount is nonzero.
    assert.neq r0 0u64;

    // Unbond the specified amount of microcredits to the caller.
    finalize self.caller r0;

finalize unbond_delegator:
    // Input the delegator's address.
    input r0 as address.public;
    // Input the amount of microcredits to unbond.
    input r1 as u64.public;

    // Check if the caller is a validator.
    contains committee[r0] into r2;
    // Enforce the caller is *not* a validator.
    assert.eq r2 false;

    // Get the bond struct for the caller, or fail if it does not exist.
    get bonded[r0] into r3;
    // Decrement the microcredits in the bond struct.
    sub r3.microcredits r1 into r4;

    // If the amount of bonded microcredits is now zero, jump to the `remove_bonded` logic.
    branch.neq r4 0u64 to remove_bonded;

    // Construct the updated bond struct.
    cast r3.validator r4 into r5 as bond;
    // Update the bond struct for the caller.
    // This will only be executed if the microcredits in the bond struct is nonzero.
    set bonded[r0] r5;

    // Proceed to continue to unbond.
    branch.eq true true to continue_to_unbond;

    // Start to remove the bond struct.
    position remove_bonded;
    // Remove the caller from the bonded mapping.
    remove bonded[r0];

    // Continue to unbond.
    position continue_to_unbond;

    // Get the stake for the specified validator.
    // If the validator does not exist, this finalize scope will fail.
    get committee[r3.validator] into r6;
    // Decrement the stake for the specified validator.
    sub r6 r1 into r7;
    // Update the stake for the specified validator.
    set committee[r3.validator] r7;

    // Construct the initial unbond struct.
    cast 0u64 0u32 into r8 as unbond;
    // Get the unbond struct for the caller, or default to the initial unbond struct.
    get.or_use unbonding[r0] r8 into r9;

    // Increment the microcredits in the unbond struct.
    add r9.microcredits r1 into r10;
    // Compute the height at which the unbonding will be complete, starting from the current block.
    // Note: Calling unbond across multiple blocks before the unbonding is complete will reset the height each time.
    add block.height 720u32 into r11;

    // Construct the updated unbond struct.
    cast r10 r11 into r12 as unbond;
    // Update the unbond struct for the caller.
    set unbonding[r0] r12;

/**********************************************************************************************************************/

function unbond_delegator_as_validator:
    // Input the delegator's address.
    input r0 as address.public;

    // Unbond the delegator as the validator.
    finalize self.caller r0;

finalize unbond_delegator_as_validator:
    // Input the validator's address.
    input r0 as address.public;
    // Input the delegator's address.
    input r1 as address.public;

    /* Start Committee */

    // Get the state for the specified validator.
    // If the validator does not exist, this finalize scope will fail.
    get committee[r0] into r2;
    // Enforce that the validator is locked.
    assert.eq r2.is_locked true;

    // Check if the delegator is a validator.
    contains committee[r1] into r3;
    // Enforce the delegator is *not* a validator.
    assert.eq r3 false;

    /* End Committee */

    /* Start Bonded */

    // Get the bond struct for the delegator, or fail if it does not exist.
    get bonded[r1] into r4;
    // Enforce that the delegator is bonded to the validator.
    assert.eq r4.validator r0;

    /* End Bonded */

    /* Start Committee */

    // Decrement the stake for the specified validator.
    sub r2.microcredits r4.microcredits into r5;
    // Construct the updated committee state.
    cast r5 r2.is_locked into r6 as state;

    /* End Committee */

    /* Start Unbond */

    // Construct the initial unbond struct.
    cast 0u64 0u32 into r7 as unbond;
    // Get the unbond struct for the delegator, or default to the initial unbond struct.
    get.or_use unbonding[r1] r7 into r8;

    // Increment the microcredits in the unbond struct.
    add r8.microcredits r4.microcredits into r9;
    // Compute the height at which the unbonding will be complete, starting from the current block.
    // Note: Calling unbond across multiple blocks before the unbonding is complete will reset the height each time.
    add block.height 720u32 into r10;

    // Construct the updated unbond struct.
    cast r9 r10 into r11 as unbond;

    /* End Unbond */

    /* Start Writes */

    // Update the stake for the specified validator.
    set r6 into committee[r0];
    // Remove the bond struct for the delegator.
    remove bonded[r1];
    // Update the unbond struct for the delegator.
    set r11 into unbonding[r1];

    /* End Writes */

/**********************************************************************************************************************/

function claim_unbond:
    // Claim the unbonded microcredits.
    finalize self.caller;

finalize claim_unbond:
    // Input the staker's address.
    input r0 as address.public;

    // Get the unbond struct for the caller, or fail if it does not exist.
    get unbonding[r0] into r1;
    // Enforce the unbonding is complete.
    assert.gte block.height r1.height;

    // Add the unbonded amount to the stakers's public balance.
    // Increments `account[r0]` by `r1`.
    // If `account[r0]` does not exist, 0u64 is used.
    // If `account[r0] + r2` overflows, `claim_unbond` is reverted.
    get.or_use account[r0] 0u64 into r2;
    add r1.microcredits r2 into r3;
    set account[r0] r3;

    // Remove the unbond struct for the caller.
    remove unbonding[r0];

/**********************************************************************************************************************/

// The `mint` function generates the specified amount
// into a record for the specified receiver.
// Note: Additional rules are enforced in consensus.
function mint:
    // Input the receiver.
    input r0 as address.public;
    // Input the amount.
    input r1 as u64.public;
    // Ensure the receiver is the caller.
    assert.eq r0 self.caller;
    // Check that the amount is less than the specified limit.
    // TODO: Reduce this to 256 credits.
    lt r1 100_000_000_000_000u64 into r2;
    // Ensure the amount is less than the specified limit.
    assert.eq r2 true;
    // Construct the receiver's record.
    cast r0 r1 into r3 as credits.record;
    // Output the receiver's record.
    output r3 as credits.record;

/**********************************************************************************************************************/

// The `transfer_public` function sends the specified amount
// from the sender's `account` to the receiver's `account`.
function transfer_public:
    // Input the receiver.
    input r0 as address.public;
    // Input the amount.
    input r1 as u64.public;
    // Transfer the credits publicly.
    finalize self.caller r0 r1;

finalize transfer_public:
    // Input the sender.
    input r0 as address.public;
    // Input the receiver.
    input r1 as address.public;
    // Input the amount.
    input r2 as u64.public;
    // Decrements `account[r0]` by `r2`.
    // If `account[r0]` does not exist, 0u64 is used.
    // If `account[r0] - r2` underflows, `transfer_public` is reverted.
    get.or_use account[r0] 0u64 into r3;
    sub r3 r2 into r4;
    set r4 into account[r0];
    // Increments `account[r1]` by `r2`.
    // If `account[r1]` does not exist, 0u64 is used.
    // If `account[r1] + r2` overflows, `transfer_public` is reverted.
    get.or_use account[r1] 0u64 into r5;
    add r5 r2 into r6;
    set r6 into account[r1];

/**********************************************************************************************************************/

// The `transfer_private` function sends the specified amount
// from the sender's record to the receiver in a record.
function transfer_private:
    // Input the sender's record.
    input r0 as credits.record;
    // Input the receiver.
    input r1 as address.private;
    // Input the amount.
    input r2 as u64.private;
    // Checks the given record has a sufficient amount.
    // This `sub` operation is safe, and the proof will fail
    // if an underflow occurs. The destination register `r3` holds
    // the change amount to be returned to the sender.
    sub r0.microcredits r2 into r3;
    // Construct a record for the specified receiver.
    cast r1 r2 into r4 as credits.record;
    // Construct a record with the change amount for the sender.
    cast r0.owner r3 into r5 as credits.record;
    // Output the receiver's record.
    output r4 as credits.record;
    // Output the sender's change record.
    output r5 as credits.record;

/**********************************************************************************************************************/

// The `transfer_private_to_public` function turns a specified amount
// from a record into public credits for the specified receiver.
//
// This function preserves privacy for the sender's record, however
// it publicly reveals the receiver and the amount.
function transfer_private_to_public:
    // Input the sender's record.
    input r0 as credits.record;
    // Input the receiver.
    input r1 as address.public;
    // Input the amount.
    input r2 as u64.public;
    // Checks the given record has a sufficient amount.
    // This `sub` operation is safe, and the proof will fail
    // if an underflow occurs. The destination register `r3` holds
    // the change amount for the sender.
    sub r0.microcredits r2 into r3;
    // Construct a record with the change amount for the sender.
    cast r0.owner r3 into r4 as credits.record;
    // Output the sender's change record.
    output r4 as credits.record;
    // Increment the amount publicly for the receiver.
    finalize r1 r2;

finalize transfer_private_to_public:
    // Input the receiver.
    input r0 as address.public;
    // Input the amount.
    input r1 as u64.public;
    // Retrieve the balance of the sender.
    // If `account[r0]` does not exist, 0u64 is used.
    get.or_use account[r0] 0u64 into r2;
    // Increments `account[r0]` by `r1`.
    // If `r1 + r2` overflows, `transfer_private_to_public` is reverted.
    add r1 r2 into r3;
    // Updates the balance of the sender.
    set r3 into account[r0];

/**********************************************************************************************************************/

// The `transfer_public_to_private` function turns a specified amount
// from the mapping `account` into a record for the specified receiver.
//
// This function preserves privacy for the receiver's record, however
// it publicly reveals the sender and the specified amount.
function transfer_public_to_private:
    // Input the receiver.
    input r0 as address.public;
    // Input the amount.
    input r1 as u64.public;
    // Construct a record for the receiver.
    cast r0 r1 into r2 as credits.record;
    // Output the record of the receiver.
    output r2 as credits.record;
    // Decrement the balance of the sender publicly.
    finalize self.caller r1;

finalize transfer_public_to_private:
    // Input the sender.
    input r0 as address.public;
    // Input the amount.
    input r1 as u64.public;
    // Retrieve the balance of the sender.
    // If `account[r0]` does not exist, 0u64 is used.
    get.or_use account[r0] 0u64 into r2;
    // Decrements `account[r0]` by `r1`.
    // If `r2 - r1` underflows, `transfer_public_to_private` is reverted.
    sub r2 r1 into r3;
    // Updates the balance of the sender.
    set r3 into account[r0];

/**********************************************************************************************************************/

// The `join` function combines two records into one.
function join:
    // Input the first record.
    input r0 as credits.record;
    // Input the second record.
    input r1 as credits.record;
    // Combines the amount of the first record and the second record.
    // This `add` operation is safe, and the proof will fail
    // if an overflow occurs.
    add r0.microcredits r1.microcredits into r2;
    // Construct a record with the combined amount.
    cast r0.owner r2 into r3 as credits.record;
    // Output the record.
    output r3 as credits.record;

/**********************************************************************************************************************/

// The `split` function splits a record into two records.
function split:
    // Input the record.
    input r0 as credits.record;
    // Input the amount to split.
    input r1 as u64.private;
    // Checks the given record has a sufficient amount to split.
    // This `sub` operation is safe, and the proof will fail
    // if an underflow occurs.
    sub r0.microcredits r1 into r2;
    // Construct the first record.
    cast r0.owner r1 into r3 as credits.record;
    // Construct the second record.
    cast r0.owner r2 into r4 as credits.record;
    // Output the first record.
    output r3 as credits.record;
    // Output the second record.
    output r4 as credits.record;

/**********************************************************************************************************************/

// The `fee` function charges the specified amount from the sender's record.
function fee:
    // Input the sender's record.
    input r0 as credits.record;
    // Input the amount.
    input r1 as u64.public;
    // Input the deployment or execution root.
    input r2 as field.public;
    // Ensure the amount is nonzero.
    assert.neq r1 0u64;
    // Checks the given record has a sufficient amount.
    // This `sub` operation is safe, and the proof will fail
    // if an underflow occurs. The destination register `r3` holds
    // the change amount for the sender.
    sub r0.microcredits r1 into r3;
    // Construct a record with the change amount for the sender.
    cast r0.owner r3 into r4 as credits.record;
    // Output the sender's change record.
    output r4 as credits.record;

/**********************************************************************************************************************/
