// Disclosure: This program is experimental and not intended for production use.
// This program is provided "as is" without warranties of any kind.
// The author disclaims liability for damages of any kind arising from the use of this program.
program stake.aleo;

// The `bond` struct tracks the amount of microcredits that are currently bonded to the specified validator.
struct bond:
    validator as address;
    microcredits as u64;

// The `stake` struct tracks the principal and delegated stake for the specified validator.
struct stake:
    principal as u64;
    delegated as u64;

// The `lock` struct track the amount of microcredits that are currently locked for the specified owner until the
// specified unlock height.
struct lock:
    owner as address;
    bond as bond;
    unlock_height as u32;

// NOTE: This stake amount is the sum of all the microcredits bonded to the validator. To get the validator's initial
// balance, we would need to subtract all the delegated stake currently in the `bonded` mapping.
mapping validators:
    key left as address.public;
    value right as stake.public;

// The `delegators` mapping represents the delegators for the specified validator.
mapping delegators:
    key left as address.public;
    value right as [address].public;

// The `bonded` mapping represents the amount of microcredits that are currently bonded.
mapping bonded:
    key left as address.public;
    value right as bond.public;

// The `locked` mapping represents the amount of microcredits that are currently locked for the owner.
mapping locked:
    key left as address.public;
    value right as [lock].public;

//
// The `bond_validator` function bonds a given number of microcredits as a validator.
//
// The following must be true for the `bond_validator` function to succeed:
// - A minimum of 1 million credits must be bonded if caller is a new validator.
function bond_validator:
    // Input the amount of microcredits to bond.
    input r0 as u64.public;

    // Determine if the amount is at least one credit.
    gte r0 1_000_000u64 into r1;
    // Enforce the amount is at least one credit.
    assert.eq r1 true;

    // Perform the transfer of microcredits from the caller to the 'stake.aleo' program.
    // call credits.aleo/transfer_public stake.aleo r1;

    finalize self.caller r0;

finalize bond_validator:
    // Input the validator address.
    input r0 as address.public;
    // Input the amount of microcredits to bond.
    input r1 as u64.public;

    // Construct the default stake struct.
    cast 0u64 0u64 into stake as r2;
    // Get the stake for the specified validator.
    get.or_use validators[r0] r2 into r3;

    // Increment the stake for the specified validator.
    add r3.principal r1 into r4;

    // Check if the stake is at least 1 million credits.
    gte r4 1_000_000_000_000u64 into r5;
    // Enforce the stake is at least 1 million credits.
    assert.eq r5 true;

    // Construct the new stake struct.
    cast r4 r3.delegated into stake as r6;

    // Update the stake for the specified validator.
    set validators[r0] r6;

//
// The `unbond_validator` function unbonds a given number of microcredits as a validator.
//
// The following must be true for the `unbond_validator` function to succeed:
// - A minimum of 1 credit must be unbonded.
function unbond_validator:
    // Input the amount of microcredits to unbond.
    input r0 as u64.public;

    // Determine if the amount is at least one credit.
    gte r1 1_000_000u64 into r0;
    // Enforce the amount is at least one credit.
    assert.eq r2 true;

    finalize self.caller r0;

finalize unbond_validator:
    // Input the validator address.
    input r0 as addres.public;
    // Input the amount of microcredits to unbond.
    input r1 as u64.public;

    // Get the stake for the specified validator.
    get validators[r0] into r2;
    // Construct the new principal stake.
    sub r2.principal r1 into r3;
    // Create the new stake struct.
    cast r3 r2.delegated into stake as r4;
    // Update the stake for the validator.
    set validators[r0] r4;

    // Construct the bond struct for the lock.
    cast r0 r1 into r5 as bond;
    // Construct the unlock height.
    add block.height 256u32 into r6;
    // Construct the lock struct.
    cast r0 r4 r6 into r7 as lock;

    // Initialize an empty vector.
    cast into r8 as [lock];
    // Add the lock to the list of locks associated with the staker.
    get.or_use locked[r0] r8 into r9;
    // Insert the new lock.
    push r9 r7;
    // Update the locks.
    set locked[r0] r9;

    // Check if the remaining stake is at least 1 million credits.
    gte r3 1_000_000_000_000u64 into r10;
    // If the remaining stake is less than 1 million credits, unbond all the delegators.
    branch.eq r10 true to skip_unbond_delegators;

    // Initialize an empty vector.
    cast into r11 as [address];
    // Get the delegators for the specified validator.
    get.or_use delegators[r0] r11 into r12;

    // Get the number of delegators.
    len r12 into r13;
    // Loop through all the delegators.
    position start_loop;
    branch.eq r13 0u64 to end_loop;
    // Remove the delegator.
    remove r11 r13 into r14;
    // Get the bond of the delegator.
    get bonded[r14] into r15;
    // TODO: Add support for calling the `finalize` scope of the `unbond_staker` function.
    // Unbond the staker.
    call unbond_staker r0 r14 r15.microcredits;
    // Decrement the index.
    sub r13 1u64 into r13;
    // Jump back to the start of the loop.
    branch.eq true true to start_loop;
    position end_loop;

    // Get the stake state of the validator.
    get validators[r0] into r16;
    // Check that the delegated stake is now zero.
    assert.eq r16.delegated 0u64;

    // The position we jump to if the validator has more than 1 million credits.
    position skip_unbond_delegators;

    // If the remaining principal stake is zero, then remove the validator.
    branch.neq r3.principal 0u64 to skip_remove_validator;
    // Remove the validator from the list of validators.
    remove validators[r0];
    // The position we jump to if the validator still has some stake.
    position skip_remove_validator;

//
// The `bond_staker` function bonds a given number of microcredits to the specified validator.
//
// The following must be true for the `bond_staker` function to succeed:
// - Bonding a minimum of 1 credit
// - The caller is not a validator
// - The validator exists
// - If the staker is already bonded, the validator must match
function bond_staker:
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
    // call credits.aleo/transfer_public stake.aleo r1;

    // Bond the specified amount of microcredits to the specified validator.
    finalize self.caller r0 r1;

finalize bond_staker:
    // Input the staker's address.
    input r0 as address.public;
    // Input the validator address.
    input r1 as address.public;
    // Input the amount of microcredits to bond.
    input r2 as u64.public;

    // Check if the caller is a validator.
    contains validators[r0] into r3;
    // Enforce the caller is not *a* validator.
    assert.eq r3 false;

    // Get the stake for the specified validator.
    // If the validator does not exist, this finalize scope will fail.
    get validators[r1] into r4;
    // Check if the validator has is at least 1 million credits.
    gte r4.principal 1_000_000_000_000u64 into r5;
    // Enforce the stake is at least 1 million credits.
    assert.eq r5 true;
    // Increment the delegated stake for the specified validator.
    add r4.delegated r2 into r6;
    // Construct the updated stake struct.
    cast r4.principal r6 into stake as r7;
    // Update the stake for the specified validator.
    set validators[r1] r7;

    // Construct the initial bond struct.
    cast r1 0u64 into r8 as bond;
    // Get the bond struct for the caller, or default to the initial bond struct.
    get.or_use bonded[r0] r8 into r9;
    // Enforce the validator matches in the bond struct.
    assert.eq r9.validator r1;

    // Increment the microcredits in the bond struct.
    add r9.microcredits r2 into r10;
    // Construct the updated bond struct.
    cast r1 r10 into r11 as bond;
    // Update the bond struct for the caller.
    set bonded[r0] r11;

//
// The `unbond_staker` function unbonds a given number of microcredits. The unbonded amount
// is locked for a specified number of blocks.
//
// The following must be true for the `unbond_staker` function to succeed:
// - Unbonded amount must be nonzero
// - Unbonded amount must be less than or equal to the staker's bonded amount
// - The caller is not a validator
function unbond_staker:
    // Input the validator address to unbond from.
    input r0 as address.public;
    // Input the amount of microcredits to unbond.
    input r1 as u64.public;

    // Determine if the amount is at least one credit.
    gte r1 1_000_000u64 into r2;
    // Enforce the amount is at least one credit.
    assert.eq r2 true;

    // Unbond the specified amount of microcredits to the caller.
    finalize self.caller r0 r1;

finalize unbond_staker:
    // Input the staker's address.
    input r0 as address.public;
    // Input the validator address.
    input r1 as address.public;
    // Input the amount of microcredits to unbond.
    input r2 as u64.public;

    // Check if the caller is a validator.
    get validators[r0] into r3;
    // Enforce the caller is not *a* validator.
    assert.eq r3 false;

    // Get the bond struct for the caller, or fail if it does not exist.
    get bonded[r0] into r4;
    // Enforce that the validator matches in the bond struct.
    assert.eq r4.validator r1;
    // Decrement the microcredits in the bond struct.
    sub r3.microcredits r2 into r5;

    // Remove the bond struct.
    remove bonded[r0];
    // If the microcredits in the bond struct is now zero, then do not update the bond struct.
    branch.eq r5 0u64 to remove_only;

    // Construct the updated bond struct.
    cast r1 r5 into r6 as bond;
    // Update the bond struct for the caller.
    set bonded[r0] r6;

    // The position we jump to if the remaining bond is zero.
    position remove_only;

    // Get the stake for the specified validator.
    // If the validator does not exist, this finalize scope will fail.
    get validators[r1] into r6;
    // Decrement the stake for the specified validator.
    sub r6.delegated r2 into r7;
    // Construct the new stake struct.
    cast r6.princial r7 into r8 as stake;
    // Update the stake for the specified validator.
    set validators[r1] r8;

    // Construct the bond struct for the lock.
    cast r1 r2 into r9 as bond;
    // Construct the unlock height.
    add block.height 256u32 into r10;
    // Construct the lock struct.
    cast r0 r9 r10 into r11 as lock;

    // Add the lock to the list of locks associated with the staker.
    get.or_use locked[r0] [] into r12;
    // Insert the new lock.
    array.append r12 r11 as r13; // TODO: Establish array syntax.
    // Update the locks.
    set locked[r0] r13;

// The `unlock_stake` function attempts to unlock the oldest lock for the staker. Anyone can unlock tokens for a staker.
// // TODO: Iterate over the locks and unlock all that qualify.
//
// The following must be true for the `unlock_stake` function to succeed:
// - The staker has at least one lock
function unlock_stake:
    // Input the staker's address.
    input r0 as address.public;

    finalize r0;

finalize unlock_stake:
    // Input the staker's address.
    input r0 as address.public;

    // Get the lock struct for the staker.
    // If the lock does not exist, this finalize scope will fail.
    get locked[r0] into r1;

    // Get the length of the locks.
    len r1 into r2; // TODO: Establish array syntax.
    // Determine if the staker has at least one lock.
    gte r2 1u64 into r3;
    // Enforce the length of the locks is at least one.
    assert.eq r3 true;

    // Get the first lock.
    array.get r1[0u32] into r4; // TODO: Establish array syntax.
    // Remove the first lock from the list.
    array.remove r1 0u32 into r5; // TODO: Establish array syntax.

    // Remove the bond struct.
    remove locked[r0];
    // Determine the new number of locks.
    len r5 into r6; // TODO: Establish array syntax.
    // If there are no more locks associated with the staker, then do not update the list of locks.
    branch.eq r6 0u32 to remove_only;

    // Update the list of locks staker.
    set locked[r0] r5;

    // The position we jump to if there are no more locks associated with the staker.
    position remove_only;

    // TODO: Add support for calling external programs (by starting with their 'function' and moving to their 'finalize').
    // Perform the transfer of microcredits from the 'stake.aleo' program to the caller.
    call credits.aleo/transfer_public r0 r4.microcredits;

// TODO: Implement slashing.
//// The `slash_stake` function slashes a percentage of stake for a validator and it's delegators.
//function slash:
//
//finalize slash:
//    // Slash the principal stake for the validator.
//
//    // Iterate through `delegators` mapping and slash each delegator's stake.
//
//    // Iterate through the locks slash the locks validator associated with the validator.
//
//    // Update the delegated stake for the validator.
//
//    // Confirm that the sum of the delegated stake is equivalent to the delegated stake stored in the `validators` mapping.
//
//    // Check if the remaining principal balance is less than 1 million credits.
//
//    // If the validator does not have 1 million credits, unbond all delegators.
