// Disclosure: This program is experimental and not intended for production use.
// This program is provided "as is" without warranties of any kind.
// The author disclaims liability for damages of any kind arising from the use of this program.
program credits.aleo;

/**********************************************************************************************************************/

/// The `committee` mapping contains the active validator set and their corresponding stake.
mapping committee:
    // The key represents the address of the validator.
    key validator as address.public;
    // The value represents the amount of microcredits bonded to the validator, by the validator and its delegators.
    value stake as u64.public;

/**********************************************************************************************************************/

// The `bonded` mapping represents the amount of microcredits that are currently bonded.
mapping bonded:
    // The key represents the address of the staker, which includes the validators and their delegators.
    key staker as address.public;
    // The value represents the bond.
    value bond as bond.public;

// The `bond` struct tracks the amount of microcredits that are currently bonded to the specified validator.
struct bond:
    // The key represents the address of the validator.
    validator as address;
    // The value represents the amount of microcredits that are currently bonded to the specified validator.
    microcredits as u64;

/**********************************************************************************************************************/

mapping unbonding:
    key staker as address.public;
    value unbond as unbond.public;

struct unbond:
    microcredits as u64;
    height as u32;

/**********************************************************************************************************************/

// The `account` mapping is used to store credits publicly.
mapping account:
    key owner as address.public;
    value microcredits as u64.public;

// The `credits` record is used to store credits privately.
record credits:
    owner as address.private;
    microcredits as u64.private;

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

// fn bond_validator
// - if the bond is now 33% or more, lock the validator. (determine how hard to impl this)

// fn unbond_validator
//  - can only be triggered after the validator has unbonded all of their delegators.
//  - does it matter if the validator is locked here?

// fn unbond_delegator_as_validator
//  - can only trigger this when the validator is locked.

// Useful for when you want to lock your validator from others bonding more.
// i.e. you as validator want to unbond yourself, or say you're approaching 33% of the total stake.
// fn lock_validator

// Allows you and others to bond more to your validator.
// fn unlock_validator

/**********************************************************************************************************************/

function bond_delegator:
    // Input the validator address.
    input r0 as address.public;
    // Input the amount of microcredits to bond.
    input r1 as u64.public;

    // Enforce the caller is not *the* validator.
    // Callers who wish to be a validator must use the `bond_validator` function.
    assert.neq self.caller r0;

    // Determine if the amount is at least one credit.
    gte r1 1_000_000u64 into r2;
    // Enforce the amount is at least one credit.
    assert.eq r2 true;

    // Perform the transfer of microcredits from the caller to the 'stake.aleo' program.
    call credits.aleo/transfer_public stake.aleo r1;

    // Bond the specified amount of microcredits to the specified validator.
    finalize self.caller r0 r1;

finalize bond_delegator:
    // Input the delegator's address.
    input r0 as address.public;
    // Input the validator address.
    input r1 as address.public;
    // Input the amount of microcredits to bond.
    input r2 as u64.public;

    // Check if the caller is a validator.
    contains committee[r0] into r3;
    // Enforce the caller is not *a* validator.
    assert.eq r3 false;

    // Get the stake for the specified validator.
    // If the validator does not exist, this finalize scope will fail.
    get committee[r1] into r4;
    // Increment the stake for the specified validator.
    add r4 r2 into r5;
    // Update the stake for the specified validator.
    set committee[r1] r5;

    // Construct the initial bond struct.
    cast r1 0u64 into r6 as bond;
    // Get the bond struct for the caller, or default to the initial bond struct.
    get.or_use bonded[r0] r6 into r7;
    // Enforce the validator matches in the bond struct.
    assert.eq r7.validator r1;

    // Increment the microcredits in the bond struct.
    add r7.microcredits r2 into r8;
    // Construct the updated bond struct.
    cast r1 r8 into r9 as bond;
    // Update the bond struct for the caller.
    set bonded[r0] r9;

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
    // Enforce the caller is not *a* validator.
    assert.eq r2 false;

    // Get the bond struct for the caller, or fail if it does not exist.
    get bonded[r0] into r3;
    // Decrement the microcredits in the bond struct.
    sub r3.microcredits r1 into r4;

    // TODO: Add jump to skip if 'r4' is now '0', as you can 'remove'. Otherwise, the address can only bond to the same validator forever.
    // Construct the updated bond struct.
    cast r3.validator r4 into r5 as bond;
    // Update the bond struct for the caller.
    set bonded[r0] r5;

    // Get the stake for the specified validator.
    // If the validator does not exist, this finalize scope will fail.
    get committee[r3.validator] into r6;
    // Decrement the stake for the specified validator.
    sub r6 r1 into r7;
    // Update the stake for the specified validator.
    set committee[r3.validator] r7;

    // Construct the default unbond struct.
    cast 0u64 0u32 into r8 as unbond;
    // Get the unbond struct for the caller, or default to the default unbond struct.
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

    // Perform the transfer of microcredits from the 'stake.aleo' program to the caller.
    call credits.aleo/transfer_public r0 r1.microcredits;

    // Remove the unbond struct for the caller.
    remove unbonding[r0];

//    // TODO: Add support for calling external programs (by starting with their 'function' and moving to their 'finalize').
//    // Perform the transfer of microcredits from the 'stake.aleo' program to the caller.
//    call credits.aleo/transfer_public r0 r1;

// Open Questions:
// - Should the 720 be more?
