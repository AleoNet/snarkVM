program credits.aleo;

mapping account:
    key owner as address.public;
    value microcredits as u64.public;

record credits:
    owner as address.private;
    microcredits as u64.private;

function mint:
    input r0 as address.public;
    input r1 as u64.public;
    assert.eq r0 self.caller;
    lt r1 256_000_000u64 into r2;
    assert.eq r2 true;
    cast r0 r1 into r3 as credits.record;
    output r3 as credits.record;

function transfer:
    input r0 as credits.record;
    input r1 as address.private;
    input r2 as u64.private;
    sub r0.microcredits r2 into r3;
    cast r1 r2 into r4 as credits.record;
    cast r0.owner r3 into r5 as credits.record;
    output r4 as credits.record;
    output r5 as credits.record;

/* Begin Experimental */

// The function `transfer_public_to_private` turns a specified token amount
// from the mapping `account` into a record for the specified receiver.
//
// This function preserves privacy for the receiver's record, however
// it publicly reveals the caller and the specified token amount.
function transfer_public_to_private:
    // Input the receiver.
    input r0 as address.public;
    // Input the amount.
    input r1 as u64.public;
    // Produce a record for the receiver.
    cast r0 r1 into r2 as credits.record;
    // Output the record of the receiver.
    output r2 as credits.record;
    // Decrement the balance of the caller publicly.
    finalize self.caller r1;

finalize transfer_public_to_private:
    // Input the sender.
    input r0 as address.public;
    // Input the amount.
    input r1 as u64.public;
    // Retrieve the balance of the sender.
    // If `account[r0]` does not exist, it will be created.
    get.or_init account[r0] 0u64 into r2;
    // Decrements `account[r0]` by `r1`.
    // If `r2 - r1` underflows, `transfer_public_to_private` is reverted.
    sub r2 r1 into r3;
    // Updates the balance of the sender.
    set r3 into account[r0];

/* End Experimental */

function join:
    input r0 as credits.record;
    input r1 as credits.record;
    add r0.microcredits r1.microcredits into r2;
    cast r0.owner r2 into r3 as credits.record;
    output r3 as credits.record;

function split:
    input r0 as credits.record;
    input r1 as u64.private;
    sub r0.microcredits r1 into r2;
    cast r0.owner r1 into r3 as credits.record;
    cast r0.owner r2 into r4 as credits.record;
    output r3 as credits.record;
    output r4 as credits.record;

function fee:
    input r0 as credits.record;
    input r1 as u64.public;
    input r2 as field.public;
    assert.neq r1 0u64;
    sub r0.microcredits r1 into r3;
    cast r0.owner r3 into r4 as credits.record;
    output r4 as credits.record;
