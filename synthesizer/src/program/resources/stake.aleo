// Disclosure: This program is experimental and not intended for production use.
// This program is provided "as is" without warranties of any kind.
// The author disclaims liability for damages of any kind arising from the use of this program.
program stake.aleo;

mapping validators:
    key validator as address.public;
    value stake as u64.public;

// The `bond` struct tracks the amount of microcredits
// that are currently bonded to the specified validator.
struct bond:
    validator as address;
    microcredits as u64;

// The `bonded` mapping represents the amount of microcredits
// that are currently bonded.
mapping bonded:
    key owner as address.public;
    value bond as bond.public;

finalize bond_staker:
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

    // Check if the caller is a validator.
    contains validators[self.caller] into r3;
    // Enforce the caller is not *a* validator.
    assert.eq r3 false;

    // Get the stake for the specified validator.
    // If the validator does not exist, this finalize scope will fail.
    get validators[r0] into r4;
    // Increment the stake for the specified validator.
    add r4 r1 into r5;
    // Update the stake for the specified validator.
    set validators[r0] r5;

    // Construct the initial bond struct.
    cast r0 0u64 into r6 as bond;
    // Get the bond struct for the caller, or default to the initial bond struct.
    get.or_use bonded[self.caller] r6 into r7;
    // Enforce the validator matches in the bond struct.
    assert.eq r7.validator r0;

    // Increment the microcredits in the bond struct.
    add r7.microcredits r1 into r8;
    // Construct the updated bond struct.
    cast r0 r8 into r9 as bond;
    // Update the bond struct for the caller.
    set bonded[self.caller] r9;

    // Perform the transfer of microcredits from the caller to the 'stake.aleo' program.
    call.finalize credits.aleo/transfer_public stake.aleo r1;

finalize unbond_staker:
    // Input the amount of microcredits to unbond.
    input r0 as u64.public;

    // Enforce the amount is nonzero.
    assert.neq r0 0u64;

    // r1 - unused.

    // Check if the caller is a validator.
    contains validators[self.caller] into r2;
    // Enforce the caller is not *a* validator.
    assert.eq r2 false;

    // Get the bond struct for the caller, or fail if it does not exist.
    get bonded[self.caller] into r3;
    // Decrement the microcredits in the bond struct.
    sub r3.microcredits r0 into r4;

    // TODO: Add jump to skip if 'r4' is now '0', as you can 'remove'. Otherwise, the address can only bond to the same validator forever.
    // Construct the updated bond struct.
    cast r3.validator r4 into r5 as bond;
    // Update the bond struct for the caller.
    set bonded[self.caller] r5;

    // Get the stake for the specified validator.
    // If the validator does not exist, this finalize scope will fail.
    get validators[r3.validator] into r6;
    // Decrement the stake for the specified validator.
    sub r6 r0 into r7;
    // Update the stake for the specified validator.
    set validators[r3.validator] r7;

    // TODO: Add support for calling external programs (by starting with their 'function' and moving to their 'finalize').
    // Perform the transfer of microcredits from the 'stake.aleo' program to the caller.
    call.finalize credits.aleo/transfer_public self.caller r0;

    // Call to lock the caller's microcredits for the specified number of blocks.
    call.finalize credits.aleo/lock_public r0 256u32;
