// Disclosure: This program is experimental and not intended for production use.
// This program is provided "as is" without warranties of any kind.
// The author disclaims liability for damages of any kind arising from the use of this program.
import credits.aleo;

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
    owned_by as address;
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
    // call credits.aleo/transfer_public stake.aleo r1; // TODO (raychu86): We do not have program addresses yet.

    finalize self.caller r0;

finalize bond_validator:
    // Input the validator address.
    input r0 as address.public;
    // Input the amount of microcredits to bond.
    input r1 as u64.public;

    // Construct the default stake struct.
    cast 0u64 0u64 into r2 as stake;
    // Get the stake for the specified validator.
    get.or_use validators[r0] r2 into r3;

    // Increment the stake for the specified validator.
    add r3.principal r1 into r4;

    // Check if the stake is at least 1 million credits.
    gte r4 1_000_000_000_000u64 into r5;
    // Enforce the stake is at least 1 million credits.
    assert.eq r5 true;

    // Construct the new stake struct.
    cast r4 r3.delegated into r6 as stake;

    // Update the stake for the specified validator.
    set r6 into validators[r0];

    // Initialize an entry in the delegators mapping for the specified validator.
    cast into r7 as [address];
    set r7 into delegators[r0];

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
    // call credits.aleo/transfer_public stake.aleo r1; // TODO (raychu86): We do not have program addresses yet.

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
    // If the validator does not exist, this command will fail.
    get validators[r1] into r4;
    // Enforce that the validator stake is at least 1 million credits.
    // TODO: Is this needed?
    gte r4.principal 1_000_000_000_000u64 into r5;
    // Enforce the stake is at least 1 million credits.
    assert.eq r5 true;
    // Increment the delegated stake for the specified validator.
    add r4.delegated r2 into r6;
    // Construct the updated stake struct.
    cast r4.principal r6 into r7 as stake;
    // Update the stake for the specified validator.
    set r7 into validators[r1];

    // Check if the staker is already bonded.
    contains bonded[r0] into r8;
    // If the staker is not already bonded, then add their address to the `delegators` mapping.
    branch.eq r8 true to end_update_delegators;
    // Get the delegators for the specified validator.
    get delegators[r1] into r9;
    // Add the staker's address to the delegators for the specified validator.
    push r9 r0;
    // Update the delegators for the specified validator.
    set r9 into delegators[r1];

    position end_update_delegators;

    // Construct the initial bond struct.
    cast r1 0u64 into r10 as bond;
    // Get the bond struct for the caller, or default to the initial bond struct.
    get.or_use bonded[r0] r10 into r11;
    // Enforce the validator matches in the bond struct.
    assert.eq r11.validator r1;

    // Increment the microcredits in the bond struct.
    add r11.microcredits r2 into r12;
    // Construct the updated bond struct.
    cast r1 r12 into r13 as bond;
    // Update the bond struct for the caller.
    set r13 into bonded[r0];

//
// The `unbond_validator` function unbonds a given number of microcredits as a validator.
//
// The following must be true for the `unbond_validator` function to succeed:
// - A minimum of 1 credit must be unbonded.
function unbond_validator:
    // Input the amount of microcredits to unbond.
    input r0 as u64.public;

    // Determine if the amount is at least one credit.
    gte r0 1_000_000u64 into r1;
    // Enforce the amount is at least one credit.
    assert.eq r1 true;

    finalize self.caller r0;

finalize unbond_validator:
    // Input the validator address.
    input r0 as address.public;
    // Input the amount of microcredits to unbond.
    input r1 as u64.public;

    // Get the stake for the specified validator.
    get validators[r0] into r2;
    // Construct the new principal stake.
    sub r2.principal r1 into r3;
    // Create the new stake struct.
    cast r3 r2.delegated into r4 as stake;
    // Update the stake for the validator.
    set r4 into validators[r0];

    // Construct the bond struct for the lock.
    cast r0 r1 into r5 as bond;
    // Construct the unlock height.
    add block.height 256u32 into r6;
    // Construct the lock struct.
    cast r0 r5 r6 into r7 as lock;

    // Initialize an empty vector.
    cast into r8 as [lock];
    // Add the lock to the list of locks associated with the staker.
    get.or_use locked[r0] r8 into r9;
    // Insert the new lock.
    push r9 r7;
    // Update the locks.
    set r9 into locked[r0];

    // Check if the remaining stake is at least 1 million credits.
    gte r3 1_000_000_000_000u64 into r10;
    // If the remaining stake is less than 1 million credits, unbond all the delegators.
    branch.eq r10 true to skip_unbond_delegators;

    // Initialize an empty vector.
    cast into r11 as [address];
    // Get the delegators for the specified validator.
    get.or_use delegators[r0] r11 into r12;

    // Get the number of delegators.
    length r12 into r13;
    // Loop over the delegators and unbond them.
    for r14 in 0u32..r13:
        // Remove the delegator from the vector.
        delete r12 r14 into r15;
        // Get the bond of the delegator.
        get bonded[r15] into r16;
        // Unbond the staker.
        // call unbond_staker r0 r15 r16.microcredits; // TODO: Add support for calling the `finalize` scope of the `unbond_staker` function.
    end.for;

    // Get the stake state of the validator.
    get validators[r0] into r17;
    // Check that the delegated stake is now zero.
    assert.eq r17.delegated 0u64;

    // The position we jump to if the validator has more than 1 million credits.
    position skip_unbond_delegators;

    // If the remaining principal stake is zero, then remove the validator.
    branch.neq r4.principal 0u64 to skip_remove_validator;
    // Remove the validator from the list of validators.
    remove validators[r0];
    // The position we jump to if the validator still has some stake.
    position skip_remove_validator;


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
    contains validators[r0] into r3;
    // Enforce the caller is not *a* validator.
    assert.eq r3 false;

    // Get the bond struct for the caller, or fail if it does not exist.
    get bonded[r0] into r4;
    // Enforce that the validator matches in the bond struct.
    assert.eq r4.validator r1;
    // Decrement the microcredits in the bond struct.
    sub r4.microcredits r2 into r5;

    // Remove the bond struct.
    remove bonded[r0];
    // If the microcredits in the bond struct is now zero, then do not update the bond struct.
    branch.eq r5 0u64 to remove_only;

    // Enforce that there is at least one microcredit remaining.
    gte r5 1_000_000u64 into r6;
    assert.eq r6 true;
    // Construct the updated bond struct.
    cast r1 r5 into r7 as bond;
    // Update the bond struct for the caller.
    set r7 into bonded[r0];

    // The position we jump to if the remaining bond is zero.
    position remove_only;

    // Get the stake for the specified validator.
    // If the validator does not exist, this finalize scope will fail.
    get validators[r1] into r8;
    // Decrement the stake for the specified validator.
    sub r8.delegated r2 into r9;
    // Construct the new stake struct.
    cast r8.principal r9 into r10 as stake;
    // Update the stake for the specified validator.
    set r10 into validators[r1];

    // If the remaining stake is zero, then remove the staker from the list of delegators.
    // TODO: Under the minimum?
    branch.neq r9 0u64 to skip_remove_delegator;
    // Get the delegators for the specified validator.
    get delegators[r1] into r11;
    // Remove the delegator from the list of delegators.
    // Get the length of the list of delegators.
    length r11 into r12;
    // Loop through all the delegators.
    for r13 in 0u32..r12:
        // Get the delegator at the current position.
        index r11 r13 into r14;
        // Check if the delegator matches the staker.
        is.eq r14 r0 into r15;
        // If the delegator does not match the staker, then skip to the end of the current iteration.
        branch.neq r15 true to remove_delegator;
        // Remove the delegator from the list of delegators.
        delete r11 r13 into r16;
        // Mark the end of the current iteration.
        position end_iteration;
    end.for;

    // Set the updated list of delegators.
    set r11 into delegators[r1];

    // The position we jump to if staker should not be removed.
    position skip_remove_delegator;

    // Construct the bond struct for the lock.
    cast r1 r2 into r17 as bond;
    // Construct the unlock height.
    add block.height 256u32 into r18;
    // Construct the lock struct.
    cast r0 r17 r18 into r19 as lock;

    // Initialize an empty vector.
    cast into r20 as [lock];
    // Add the lock to the list of locks associated with the staker.
    get.or_use locked[r0] r20 into r21;
    // Insert the new lock.
    push r21 r19;
    // Update the locks.
    set r21 into locked[r0];


// The `unlock_stake` function attempts to unlock all valid locks for the staker.
// Anyone can unlock tokens for a staker.
function unlock_stake:
    // Input the staker's address.
    input r0 as address.public;

    finalize r0;

finalize unlock_stake:
    // Input the staker's address.
    input r0 as address.public;

    // Get the locks for the staker.
    // If an entry in the mapping does not exist, this command will fail.
    get locked[r0] into r1;

    // Get the length of the locks.
    length r1 into r2;
    // Iterate through the locks, unlocking any that are valid.
    for r3 in 0u32..r2:
        // Get the lock from the list.
        index r1 r3 into r4;
        // If the unlock height is greater than the current block height, then the lock is not yet valid.
        // Nor will any subsequent locks be valid, so we can exit the loop.
        gt r4.unlock_height block.height into r5;
        branch.eq r5 true to end_iteration;
        // Otherwise, the lock is valid, so we can unlock the microcredits.
        // Remove the lock.
        delete r1 r3 into r6;
        // TODO: Add support for calling external programs (by starting with their 'function' and moving to their 'finalize').
        // Perform the transfer of microcredits from the 'stake.aleo' program to the caller.
        // call.finalize credits.aleo/transfer_public r0 r4.microcredits; // TODO: Add support for calling the `finalize` scope of the `unbond_staker` function.

        // Mark the end of the current iteration.
        position end_iteration;
    end.for;

    // Update the list of locks for the staker.
    set r1 into locked[r0];
