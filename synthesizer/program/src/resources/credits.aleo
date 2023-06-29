// Disclosure: This program is experimental and not intended for production use.
// This program is provided "as is" without warranties of any kind.
// The author disclaims liability for damages of any kind arising from the use of this program.
program credits.aleo;

// The `account` mapping is used to store credits publicly.
mapping account:
    key owner as address.public;
    value microcredits as u64.public;

// The `credits` record is used to store credits privately.
record credits:
    owner as address.private;
    microcredits as u64.private;

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
