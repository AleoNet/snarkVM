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

/********************************************** INVARIANTS ************************************************************/

// 1. contains committee[r0] =>
//   a. contains delegated[r0]
//      - The set of delegated addresses is superset of active validators.
// 2. delegated[*] >= 10,000
//   a. contain bonded[*].microcredits >= 10,000
//      - Delegators can bond to any address with the 10,000 credit minimum
// 3. delegated[r0] < 10,000,000 =>
//   a. !contain committee[r0]
//      - If the delegated total (which includes the self bond) is less than 10,000,000 credits, it won't be in the committee
// 4. bond[r0].validator == r0 =>
//   a. contains committee[r0]
//     - Self bonded addresses are always active validators. Delegators **can** force validators to unbond by removing sufficient delegation
// 5. committee[r0] =>
//   a. bonded[r0].microcredits >= 100 credits
//      - Self bonded addresses are always active validators with at least 100 credits self bonded
//   b. delegated[r0] >= 10,000,000 credits
//      - The total delegated amount for an active validator is at least 10,000,000 credits
// 6. delegated[r0] == sum bond[*].microcredits by bond[].validator == r0
// 7. bond[r0].microcredits < 10,000 =>
//   a. bond[r0].validator == r0
//   b. contains committee[r0]
//   - A bond value < 10,000 implies self-bonded active validator.
// 8. bond[r0].validator != r0 =>
//   a. bond[r0].microcredits >= 10,000
// 9. count bonded[] - count committee[] == metadata[aleo1qgqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqanmpl0]
// 10. count committee[] == metadata[aleo1qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq3ljyzc]
// 11. 100,000 >= count bonded[] >= count delegated[] >= count committee[]
// 12. bond[*].microcredits > 100
// 13. delegated[*] > 10,000

/**********************************************************************************************************************/

program credits.aleo;

/**********************************************************************************************************************/

/// The `committee` mapping contains the active validator set and their corresponding stake.
mapping committee:
    // The key represents the address of the validator.
    key as address.public;
    // The value represents the committee state of the validator.
    value as committee_state.public;

// The `committee_state` struct tracks the total stake of the validator, and whether they are open to new stakers.
struct committee_state:
    // The boolean flag indicating if the validator is open to new stakers.
    is_open as boolean;
    // The percent (0-100) of delegator commissions which validator retains.
    // Set by validator on bond_validator
    commission as u8;

/**********************************************************************************************************************/

// This mapping tracks total amount bonded to an address by a validator and its delegators.
// It includes all validators whether or not they are yet part of the committee
mapping delegated:
    // The key represents the address stake is delegated to. It may not yet be a validator.
    key as address.public;
    // The amount of microcredits bonded to the validator by delegators and not the validator.
    value as u64.public;

/**********************************************************************************************************************/

/// The `metadata` mapping stores:
///   - The number of members in the committee.
///   - The number of delegators.
mapping metadata:
    // The key represents the index at which the count is stored.
    //    - This address (aleo1qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq3ljyzc) stores the number of **members** in the committee.
    //    - This address (aleo1qgqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqanmpl0) stores the number of **delegators**.
    key as address.public;
    // The value represents the count.
    value as u32.public;

/**********************************************************************************************************************/

// The `bonded` mapping represents the amount of microcredits that are currently bonded.
mapping bonded:
    // The key represents the address of the staker, which includes the validators and their delegators.
    key as address.public;
    // The value represents the bond state.
    value as bond_state.public;

// The `bond_state` struct tracks the amount of microcredits that are currently bonded to the specified validator.
struct bond_state:
    // The address of the validator.
    validator as address;
    // The amount of microcredits that are currently bonded to the specified validator.
    microcredits as u64;

/**********************************************************************************************************************/

// The `unbonding` mapping contains a set of stakers with their unbonding microcredits and unlock height.
mapping unbonding:
    // The key represents the address of the staker, which includes the validators and their delegators.
    key as address.public;
    // The value represents the unbond state.
    value as unbond_state.public;

// The `unbond_state` struct tracks the microcredits that are currently unbonding, along with the unlock height.
struct unbond_state:
    // The amount of microcredits that are currently unbonding.
    microcredits as u64;
    // The block height at which the unbonding will be complete, and can be claimed.
    height as u32;

/**********************************************************************************************************************/

// The `account` mapping is used to store credits publicly.
mapping account:
    // The key represents the address of the owner.
    key as address.public;
    // The value represents the amount of public microcredits that belong to the specified owner.
    value as u64.public;

/**********************************************************************************************************************/

// The `withdraw` mapping contains the staking address and their corresponding withdrawal address.
mapping withdraw:
    // The key represents the staking address of the owner.
    key as address.public;
    // The value represents the withdrawal address of the owner.
    value as address.public;

/**********************************************************************************************************************/

// The `credits` record is used to store credits privately.
record credits:
    // The address of the owner.
    owner as address.private;
    // The amount of private microcredits that belong to the specified owner.
    microcredits as u64.private;

/**********************************************************************************************************************/

// bond_validator is used to initiall bond a validator into the active committee.
// bond_validator can also be used to increase the self-bond of the validator.
function bond_validator:
    input r0 as address.public;  // Withdrawal address.
    input r1 as u64.public;      // Amount of microcredits to bond.
    input r2 as u8.public;       // Commission rate.

    // Determine if the amount is at least 1 credits.
    gte r1 1_000_000u64 into r3;
    // Enforce the amount is at least 1 credits.
    assert.eq r3 true;

    // Commission must be a percentage in the range 0-100 inclusive.
    gt r2 100u8 into r4;
    assert.neq r4 true;

    // Bond the specified amount of microcredits to the specified validator.
    async bond_validator self.signer r0 r1 r2 into r5;
    // Output the finalize future.
    output r5 as credits.aleo/bond_validator.future;

finalize bond_validator:
    input r0 as address.public;  // Validator's address.
    input r1 as address.public;  // Withdrawal address.
    input r2 as u64.public;      // Amount of microcredits to bond.
    input r3 as u8.public;       // Commission rate.

    // Construct the initial committee state.
    // Note: We set the initial 'is_open' state to 'true'.
    cast true r3 into r4 as committee_state;
    // Retrieve the committee state of the specified validator.
    get.or_use committee[r0] r4 into r5;

    // Fail if attempting to change commission. Commission can only be set when validator bonds the first time.
    assert.eq r3 r5.commission;

    // Construct the updated committee state.
    cast r5.is_open r5.commission into r6 as committee_state;

    /* Bonded */

    // Construct the initial bond state.
    cast r0 0u64 into r7 as bond_state;
    // Get the bond state for the caller, or default to the initial bond state.
    get.or_use bonded[r0] r7 into r8;
    // Enforce the validator matches in the bond state.
    assert.eq r8.validator r0;
    
    // Increment the microcredits in the bond state.
    add r8.microcredits r2 into r9;

    // Include total pre-delegated amount when deciding if validator has enough credits to join committee.
    // First get the current delegated amount, or start with 0 if none delegated.
    get.or_use delegated[r0] 0u64 into r10;
    // Self-bond amount + existing delegated amount = total bond.
    add r2 r10 into r11;
    // Determine if the amount is at least 10 million credits.
    gte r11 10_000_000_000_000u64 into r12;
    // Enforce the amount is at least 10 million credits.
    assert.eq r12 true;

    // Construct the updated bond state.
    cast r0 r9 into r13 as bond_state;

    /* Account */

    // Get the balance of the caller.
    // If the account does not exist, this finalize scope will fail.
    get account[r0] into r14;
    // Decrement the balance of the caller.
    sub r14 r2 into r15;

    /* Writes */

    // if (new_validator)
    contains committee[r0] into r16;
    branch.eq r16 true to validator_in_committee;
    // {
        // Check if initial bond amount is at least 100 credits
        gte r2 100_000_000u64 into r17;
        // Assert that initial self bond is at least 100 credits
        assert.eq r17 true;

        // Get the committee size.
        get.or_use metadata[aleo1qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq3ljyzc] 0u32 into r18;
        // Increment the committee size by one.
        add r18 1u32 into r19;
        // Set the new committee size.
        set r19 into metadata[aleo1qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq3ljyzc];
        // Set the withdrawal address.
        set r1 into withdraw[r0];

        // Get current unbonding state
        contains unbonding[r0] into r20;
        // Fail if current unbonding state
        assert.eq r21 false;
    // }

    position validator_in_committee;

    // Update the committee state of the specified validator.
    set r6 into committee[r0];
    // Update the bond state for the caller.
    set r13 into bonded[r0];
    // Update the balance of the caller.
    set r15 into account[r0];
    // Update the delegated amount.
    set r11 into delegated[r0];

/**********************************************************************************************************************/

// This function allows any staker to bond their microcredits to a validator and specify a withdrawal address.
// The corresponding functions for 'bond_public' are 'unbond_public' and 'claim_unbond_public'.
function bond_public:
    input r0 as address.public;  // Validator's address.
    input r1 as address.public;  // Withdrawal address.
    input r2 as u64.public;      // Amount of microcredits to bond.

    // Determine if the amount is at least one credit.
    gte r2 1_000_000u64 into r3;
    // Enforce the amount is at least one credit.
    assert.eq r3 true;

    // Do not allow self-bonding. Validators start with bond_validator.
    assert.neq self.caller r0;

    // Bond the specified amount of microcredits to the specified validator.
    async bond_public self.caller r0 r1 r2 into r4;
    // Output the finalize future.
    output r4 as credits.aleo/bond_public.future;

finalize bond_public:
    input r0 as address.public;  // Staker's address.
    input r1 as address.public;  // Validator's address.
    input r2 as address.public;  // Withdrawal address.
    input r3 as u64.public;      // Amount of microcredits to bond.

    // Retrieve the withdrawal address for the staker.
    get.or_use withdraw[r0] r2 into r4;
    // Ensure that the withdrawal address is consistent.
    assert.eq r2 r4;

    // Check if the delegator is already bonded to the validator.
    contains bonded[r0] into r5;
    branch.eq r5 true to continue_bond_delegator;
    // {
        // Ensure that the validator is open to new stakers. For pre-bond Default to is_open true.
        cast true 0u8 into r6 as committee_state;
        get.or_use committee[r1] r6 into r7;
        assert.eq r7.is_open true;

        // Get the number of delegators.
        get.or_use metadata[aleo1qgqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqanmpl0] 0u32 into r8;
        // Increment the number of bonded delegators by one.
        add r8 1u32 into r9;
        // Determine if the number of delegators is less than or equal to 100_000.
        lte r9 100_000u32 into r10;
        // Enforce that the number of delegators is less than or equal to 100_000.
        assert.eq r10 true;
        // Set the new number of delegators.
        set r9 into metadata[aleo1qgqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqanmpl0];
        // Set the withdrawal address.
        set r2 into withdraw[r0];
    // }
    
    position continue_bond_delegator;

    /* Bonded */

    // Construct the initial bond state.
    cast r1 0u64 into r11 as bond_state;
    // Get the bond state for the caller, or default to the initial bond state.
    get.or_use bonded[r0] r11 into r12;
    // Enforce the validator matches in the bond state.
    assert.eq r12.validator r1;

    // Increment the microcredits in the bond state.
    add r12.microcredits r3 into r13;

    // Determine if the amount is at least 10 thousand credits.
    gte r13 10_000_000_000u64 into r14;
    // Enforce the amount is at least 10 thousand credits.
    assert.eq r14 true;

    // Construct the updated bond state.
    cast r1 r13 into r15 as bond_state;

    /* Account */

    // Get the balance of the caller.
    // If the account does not exist, this finalize scope will fail.
    get account[r0] into r16;
    // Decrement the balance of the caller.
    sub r16 r3 into r17;

    /* Writes */

    // Update the bond state for the caller.
    set r15 into bonded[r0];
    // Update the balance of the caller.
    set r17 into account[r0];
    // Update total delegated amount.
    // Get current total delegated amount.
    get.or_use delegated[r1] 0u64 into r22;
    // Add new bond amount to current delegation.
    add r3 r22 into r23;
    // Update delegated amount.
    set r23 into delegated[r1];

/**********************************************************************************************************************/

// Unbond a staker using their associated withdrawal address
// **Validators**: It will remove the validator if the self bonded balance falls below 100 credits
// or the total delegated balance falls below 10M credits.
// **Delegators**: It will remove the validator if the total delegated balance falls below 10M credits.
// It will remove the entire bond_state of the delegator if it falls below 10,000 credits.
//
// Validators can also forcibly unbond a delegator

function unbond_public:
    input r0 as address.public; // The address of the validator or delegator to unbond.
    input r1 as u64.public;     // Amount of microcredits to unbond.

    // Unbond the specified amount of microcredits for the specified validator.
    async unbond_public self.caller r0 r1 into r2;
    // Output the finalize future.
    output r2 as credits.aleo/unbond_public.future;

finalize unbond_public:
    input r0 as address.public; // Address of the caller.
    input r1 as address.public; // Address of the validator or delegator.
    input r2 as u64.public;     // Amount of microcredits to unbond.

    /* Setup unbond public */
    // Set default unbonding state.
    add block.height 360u32 into r3;
    cast 0u64 r3 into r4 as unbond_state;
    /* End setup unbond public */

    // Retrieve the bond state of the validator or delegator, or fail if no bond state exists.
    get bonded[r1] into r5;

    /* Check Caller Permission */
    // Get the withdrawal address of the validator or delegator.
    get withdraw[r1] into r6; 
    // Get the withdrawal address of the validator from the bond state.
    get withdraw[r5.validator] into r7;
    is.eq r0 r6 into r8;
    is.eq r0 r7 into r9;
    or r8 r9 into r10;
    // Assert that the caller is the withdrawal address.
    assert.eq r10 true;
    /* End Check Caller Permission */

    // Check if bonded to self (validator) or to a different address (delegator).
    is.eq r5.validator r1 into r11;
    branch.eq r11 true to unbond_validator;

    /* Unbond Delegator */
    // {
        /* Setup Unbond Delegator */
        // Retrieve or initialize the unbonding state.
        get.or_use unbonding[r1] r4 into r12;
        // Retrieve total delegated balance for the validator.
        get delegated[r5.validator] into r13;
        /* End Setup Unbond Delegator */

        // Calculate new bonded microcredits, fail on overdraft.
        sub r5.microcredits r2 into r14;

        // Check if the delegator will have <= 10,000 credits bonded.
        lte r14 10_000_000_000u64 into r15;

        // If validator is forcing delegator to unbond or delegator will have <= 10,000 credits bonded.
        or r15 r9 into r16;

        // Determine the amount to unbond: requested amount if above 10,000 credits, otherwise the full bonded amount.
        ternary r16 r5.microcredits r2 into r17;

        /* Update Unbonding state */
        // Increment existing unbond amount by the new unbond amount.
        add r17 r12.microcredits into r18;
        // Set the updated unbond state.
        cast r18 r3 into r19 as unbond_state;
        // Store the new unbonding state.
        set r19 into unbonding[r1];
        /* End Update Unbonding state */

        /* Update Delegated State */
        // Calculate new delegated total for the validator.
        sub r13 r17 into r20;
        // Store the new delegated total.
        set r20 into delegated[r5.validator];
        /* End Update Delegated state */

        // Check if the new bonded state is below 10,000 credits or validator is forcing unbond.
        branch.eq r16 true to remove_delegator;

        /* Decrement Delegator */
        // {
            /* Update Bonded state */
            // Set the new bond state.
            cast r5.validator r14 into r21 as bond_state;
            set r21 into bonded[r1];
            /* End Update Bonded state */

            // Jump to end of unbond delegator process.
            branch.eq true true to end_unbond_delegator;
        // }

        position remove_delegator;
        // {
            /* Update Bonded state */
            // Remove the bonded state.
            remove bonded[r1];
            /* End Update Bonded state */

            /* Update Metadata */
            // Retrieve the current number of delegators.
            get.or_use metadata[aleo1qgqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqanmpl0] 0u32 into r22;
            // Decrement the number of delegators by one.
            sub r22 1u32 into r23;
            // Store the new number of delegators.
            set r23 into metadata[aleo1qgqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqanmpl0];
            /* End Update Metadata */
        // }

        position end_unbond_delegator;
        // {
            // Check if the new delegated total is below 10M credits.
            gte r20 10_000_000_000_000u64 into r24;
            // Jump to end if the delegated total is above 10M credits.
            branch.eq r24 true to end;
        // }
    //}

    /* Unbond the validator */
    position unbond_validator;
    // {
        /* Setup Unbond Validator */
        // Check if the committee contains the validator
        contains committee[r5.validator] into r25;
        // Delegator unbonding from a validator not in the committee
        nor r11 r25 into r26;
        // Jump to end if delegator unbonding from a validator not in the committee
        branch.eq r26 true to end;

        // Retrieve the committee state or fail if it doesn't exist.
        get committee[r5.validator] into r27;

        // Retrieve the bond state of the validator.
        get bonded[r5.validator] into r28;

        // Retrieve the total delegated balance for the validator.
        get delegated[r5.validator] into r29;
        /* End Setup Unbond Validator */

        // Check if the current delegated amount is below 10M credits.
        lte r29 10_000_000_000_000u64 into r30;
        branch.eq r30 true to remove_validator;

        // Calculate the new delegated total after unbonding.
        sub r29 r2 into r31;

        // Calculate the new bond state after unbonding.
        sub r28.microcredits r2 into r32;

        // Check if the new bond state is below the required minimums.
        gte r32 100u64 into r33; // Minimum self bond requirement: 100 credits.
        gte r31 10_000_000_000_000u64 into r34; // Minimum total delegated requirement: 10M credits.

        // If either bond state is below the thresholds, remove the validator from the committee.
        and r33 r34 into r35;
        branch.eq r35 false to remove_validator;

        /* Update Validator State */
        // Retrieve or initialize the unbonding state.
        get.or_use unbonding[r5.validator] r4 into r36;
        // Increment the unbond amount.
        add r36.microcredits r2 into r37;
        // Set the updated unbond state.
        cast r37 r3 into r38 as unbond_state;
        // Store the new unbonding state.
        set r38 into unbonding[r1];

        /* Update Delegated Total */
        // Store the new delegated total.
        set r31 into delegated[r1];
        /* End Update Delegated Total */

        /* Update Validator Bonded State */
        // Construct and store the new bond state.
        cast r5.validator r32 into r39 as bond_state;
        set r39 into bonded[r1];
        /* End Update Validator Bonded State */

        // Jump to end.
        branch.eq true true to end;
    //}

    /* Remove the validator from the committee */
    position remove_validator;
    // {
        // Remove the validator from the committee.
        remove committee[r5.validator];

        /* Update Metadata */
        // Retrieve the current committee size.
        get metadata[aleo1qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq3ljyzc] into r40;
        // Decrement the committee size by one.
        sub r40 1u32 into r41;
        // Store the new committee size.
        set r41 into metadata[aleo1qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq3ljyzc];
        /* End Update Metadata */

        /* Update Delegated Total */
        // Decrease the delegated total by the bonded amount.
        sub r29 r28.microcredits into r42;
        set r42 into delegated[r5.validator];
        /* End Update Delegated Total */

        /* Clear Bonded State */
        // Remove the bonded state.
        remove bonded[r5.validator];
        /* End Clear Bonded State */

        /* Update Unbonding State */
        // Retrieve or initialize the unbonding state.
        get.or_use unbonding[r5.validator] r4 into r43;
        // Increment the unbond amount by the full bonded amount.
        add r28.microcredits r43.microcredits into r44;
        // Set the updated unbond state.
        cast r44 r3 into r45 as unbond_state;
        // Store the new unbonding state.
        set r45 into unbonding[r1];
        /* End Update Unbonding State */
    //}

    position end;

/**********************************************************************************************************************/

// The `claim_unbond_public` function allows any address to run a crank to enable a staker to claim their microcredits
// to their withdrawal address after the unbonding period.
//
// This function also removes the staker's withdrawal address if the staker no longer has any bonded balance.
function claim_unbond_public:
    // The address of the staker
    input r0 as address.public;
    // The number of microcredits to claim
    input r1 as u64.public;

    // Claim the unbonded microcredits.
    async claim_unbond_public r0 r1 into r2;
    // Output the finalize future.
    output r2 as credits.aleo/claim_unbond_public.future;

finalize claim_unbond_public:
    // Input the staker's address.
    input r0 as address.public;
    // Input the number of microcredits to claim
    input r1 as u64.public;

    // Get the unbond state for the address, or fail if it does not exist.
    get unbonding[r0] into r2;
    // Assert that the claim amount is the full unbond state
    assert.eq r1 r2.microcredits;
    // Determine if unbonding is complete.
    gte block.height r2.height into r3;
    // Enforce the unbonding is complete.
    assert.eq r3 true;

    // Get the withdrawal address for the address.
    get withdraw[r0] into r4;

    // Add the unbonded amount to the withdrawal address public balance.
    // Increments `account[r4]` by `r1`.
    // If `account[r4]` does not exist, 0u64 is used.
    // If `account[r4] + r1` overflows, `claim_unbond_public` is reverted.
    get.or_use account[r4] 0u64 into r5;
    add r2.microcredits r5 into r6;
    set r6 into account[r4];

    // Remove the unbond state for the staker.
    remove unbonding[r0];

    // Check if the staker is still bonded.
    contains bonded[r0] into r7;
    // Ends the `claim_unbond_public` logic.
    branch.eq r7 true to end;

    // If the caller is no longer bonded, remove the withdrawal address.
    remove withdraw[r0];

    // The terminus.
    position end;

/**********************************************************************************************************************/

// This function allows a validator to set their state to be either opened or closed to new stakers.
// When the validator is open to new stakers, any staker (including the validator) can bond or unbond from the validator.
// When the validator is closed to new stakers, existing stakers can still bond or unbond from the validator, but new stakers cannot bond.
//
// This function serves two primary purposes:
// 1. Allow a validator to leave the committee, by closing themselves to stakers and then unbonding all of their stakers.
// 2. Allow a validator to maintain their % of stake, by closing themselves to allowing more stakers to bond to them.
function set_validator_state:
    // Input the 'is_open' state.
    input r0 as boolean.public;
    // Set the validator to be either open or closed to new stakers.
    async set_validator_state self.caller r0 into r1;
    // Output the finalize future.
    output r1 as credits.aleo/set_validator_state.future;

finalize set_validator_state:
    // Input the validator's address.
    input r0 as address.public;
    // Input the 'is_open' state.
    input r1 as boolean.public;

    // Get the committee state for the specified validator.
    // If the validator does not exist, this finalize scope will fail.
    get committee[r0] into r2;

    // Construct the updated committee state.
    cast r1 r2.commission into r3 as committee_state;
    // Update the committee state for the specified validator.
    set r3 into committee[r0];

/**********************************************************************************************************************/

// The `transfer_public` function sends the specified amount
// from the caller's `account` to the receiver's `account`.
function transfer_public:
    // Input the receiver.
    input r0 as address.public;
    // Input the amount.
    input r1 as u64.public;
    // Transfer the credits publicly.
    async transfer_public self.caller r0 r1 into r2;
    // Output the finalize future.
    output r2 as credits.aleo/transfer_public.future;

finalize transfer_public:
    // Input the caller.
    input r0 as address.public;
    // Input the receiver.
    input r1 as address.public;
    // Input the amount.
    input r2 as u64.public;
    // Decrements `account[r0]` by `r2`.
    // If `account[r0] - r2` underflows, `transfer_public` is reverted.
    get account[r0] into r3;
    sub r3 r2 into r4;
    set r4 into account[r0];
    // Increments `account[r1]` by `r2`.
    // If `account[r1]` does not exist, 0u64 is used.
    // If `account[r1] + r2` overflows, `transfer_public` is reverted.
    get.or_use account[r1] 0u64 into r5;
    add r5 r2 into r6;
    set r6 into account[r1];

/**********************************************************************************************************************/

// The `transfer_public_as_signer` function sends the specified amount
// from the signer's `account` to the receiver's `account`.
function transfer_public_as_signer:
    // Input the receiver.
    input r0 as address.public;
    // Input the amount.
    input r1 as u64.public;
    // Transfer the credits publicly.
    async transfer_public_as_signer self.signer r0 r1 into r2;
    // Output the finalize future.
    output r2 as credits.aleo/transfer_public_as_signer.future;

finalize transfer_public_as_signer:
    // Input the signer.
    input r0 as address.public;
    // Input the receiver.
    input r1 as address.public;
    // Input the amount.
    input r2 as u64.public;
    // Decrements `account[r0]` by `r2`.
    // If `account[r0] - r2` underflows, `transfer_public_as_signer` is reverted.
    get account[r0] into r3;
    sub r3 r2 into r4;
    set r4 into account[r0];
    // Increments `account[r1]` by `r2`.
    // If `account[r1]` does not exist, 0u64 is used.
    // If `account[r1] + r2` overflows, `transfer_public_as_signer` is reverted.
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
    // Increment the amount publicly for the receiver.
    async transfer_private_to_public r1 r2 into r5;
    // Output the sender's change record.
    output r4 as credits.record;
    // Output the finalize future.
    output r5 as credits.aleo/transfer_private_to_public.future;

finalize transfer_private_to_public:
    // Input the receiver.
    input r0 as address.public;
    // Input the amount.
    input r1 as u64.public;
    // Retrieve the balance of the receiver.
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
// This function publicly reveals the sender, the receiver, and the specified amount.
// However, subsequent methods using the receiver's record can preserve the receiver's privacy.
function transfer_public_to_private:
    // Input the receiver.
    input r0 as address.private;
    // Input the amount.
    input r1 as u64.public;
    // Construct a record for the receiver.
    cast r0 r1 into r2 as credits.record;
    // Decrement the balance of the sender publicly.
    async transfer_public_to_private self.caller r1 into r3;
    // Output the record of the receiver.
    output r2 as credits.record;
    // Output the finalize future.
    output r3 as credits.aleo/transfer_public_to_private.future;

finalize transfer_public_to_private:
    // Input the sender.
    input r0 as address.public;
    // Input the amount.
    input r1 as u64.public;
    // Retrieve the balance of the sender.
    get account[r0] into r2;
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

// The `split` function splits a record into two records. The given input amount will be stored in the first record,
// and the remaining amount will be stored in the second record, with the fee deducted from the remaining amount.
// If the caller executes a transaction that contains only a call to this function, then the transaction does not
// require a fee, unless the caller wishes to provide an additional fee. Transactions that contain multiple transitions
// (that include one or more calls to this function) will require a fee as per standard consensus rules.
function split:
    // Input the record.
    input r0 as credits.record;
    // Input the amount to split.
    input r1 as u64.private;
    // Checks the given record has a sufficient amount to split.
    // This `sub` operation is safe, and the proof will fail
    // if an underflow occurs.
    sub r0.microcredits r1 into r2;
    // Checks the given record has a sufficient fee to remove.
    // This `sub` operation is safe, and the proof will fail
    // if an underflow occurs.
    sub r2 10_000u64 into r3;
    // Construct the first record.
    cast r0.owner r1 into r4 as credits.record;
    // Construct the second record.
    cast r0.owner r3 into r5 as credits.record;
    // Output the first record.
    output r4 as credits.record;
    // Output the second record.
    output r5 as credits.record;

/**********************************************************************************************************************/

// The `fee_private` function charges the specified amount from the sender's record.
function fee_private:
    // Input the sender's record.
    input r0 as credits.record;
    // Input the amount.
    input r1 as u64.public;
    // Input the priority fee amount.
    input r2 as u64.public;
    // Input the deployment or execution ID.
    input r3 as field.public;
    // Ensure the amount is nonzero.
    assert.neq r1 0u64;
    // Ensure the deployment or execution ID is nonzero.
    assert.neq r3 0field;
    // Add the fee and priority fee amounts.
    add r1 r2 into r4;
    // Checks the given record has a sufficient amount.
    // This `sub` operation is safe, and the proof will fail
    // if an underflow occurs. The destination register `r3` holds
    // the change amount for the sender.
    sub r0.microcredits r4 into r5;
    // Construct a record with the change amount for the sender.
    cast r0.owner r5 into r6 as credits.record;
    // Output the sender's change record.
    output r6 as credits.record;

/**********************************************************************************************************************/

// The `fee_public` function charges the specified amount from the sender's account.
function fee_public:
    // Input the amount.
    input r0 as u64.public;
    // Input the priority fee amount.
    input r1 as u64.public;
    // Input the deployment or execution ID.
    input r2 as field.public;
    // Ensure the amount is nonzero.
    assert.neq r0 0u64;
    // Ensure the deployment or execution ID is nonzero.
    assert.neq r2 0field;
    // Add the fee and priority fee amounts.
    add r0 r1 into r3;
    // Decrement the balance of the sender publicly.
    async fee_public self.signer r3 into r4;
    // Output the finalize future.
    output r4 as credits.aleo/fee_public.future;

finalize fee_public:
    // Input the sender's address.
    input r0 as address.public;
    // Input the total fee amount.
    input r1 as u64.public;
    // Retrieve the balance of the sender.
    // If `account[r0]` does not exist, `fee_public` is reverted.
    get account[r0] into r2;
    // Decrements `account[r0]` by `r1`.
    // If `r2 - r1` underflows, `fee_public` is reverted.
    sub r2 r1 into r3;
    // Updates the balance of the sender.
    set r3 into account[r0];

/**********************************************************************************************************************/

// Open Questions:
// fn bond
// - if the bond is now 33% or more, close the validator. (determine how hard to impl this)

/**********************************************************************************************************************/
