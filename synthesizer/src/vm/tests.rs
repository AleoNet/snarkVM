// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// The snarkVM library is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// The snarkVM library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with the snarkVM library. If not, see <https://www.gnu.org/licenses/>.

use super::*;

mod credits_tests {
    use super::*;

    use crate::{Block, ConsensusMemory, Header, Metadata, Transaction, Transactions};
    use console::{
        account::{Address, ViewKey},
        program::Literal,
        types::Field,
    };

    use once_cell::sync::OnceCell;

    type CurrentNetwork = test_helpers::CurrentNetwork;

    /// Construct a new block based on the given transactions.
    fn sample_next_block<R: Rng + CryptoRng>(
        vm: &VM<CurrentNetwork, ConsensusMemory<CurrentNetwork>>,
        private_key: &PrivateKey<CurrentNetwork>,
        transactions: &[Transaction<CurrentNetwork>],
        previous_block: &Block<CurrentNetwork>,
        rng: &mut R,
    ) -> Result<Block<CurrentNetwork>> {
        // Construct the new block header.
        let transactions = Transactions::from(transactions);
        // Construct the metadata associated with the block.
        let metadata = Metadata::new(
            CurrentNetwork::ID,
            previous_block.round() + 1,
            previous_block.height() + 1,
            CurrentNetwork::GENESIS_COINBASE_TARGET,
            CurrentNetwork::GENESIS_PROOF_TARGET,
            previous_block.last_coinbase_target(),
            previous_block.last_coinbase_timestamp(),
            CurrentNetwork::GENESIS_TIMESTAMP + 1,
        )?;

        let header = Header::from(
            *vm.block_store().current_state_root(),
            transactions.to_root().unwrap(),
            Field::zero(),
            metadata,
        )?;

        Block::new(private_key, previous_block.hash(), header, transactions, None, rng)
    }

    /// Sets up a test instance and returns the VM, caller private key, an unspent record, and the genesis block.
    fn initialize_state() -> (
        VM<CurrentNetwork, ConsensusMemory<CurrentNetwork>>,
        PrivateKey<CurrentNetwork>,
        Record<CurrentNetwork, Plaintext<CurrentNetwork>>,
        Block<CurrentNetwork>,
    ) {
        static INSTANCE: OnceCell<(Block<CurrentNetwork>, PrivateKey<CurrentNetwork>)> = OnceCell::new();
        let (genesis, caller_private_key) = INSTANCE
            .get_or_init(|| {
                let rng = &mut TestRng::default();
                // Initialize the genesis block and genesis private key.
                (test_helpers::sample_genesis_block(rng), test_helpers::sample_genesis_private_key(rng))
            })
            .clone();

        // Prepare the additional fee.
        let caller_view_key = ViewKey::try_from(&caller_private_key).unwrap();
        let credits = genesis.records().next().unwrap().1.decrypt(&caller_view_key).unwrap();

        // Initialize and update the VM.
        let vm = crate::vm::test_helpers::sample_vm();
        vm.add_next_block(&genesis).unwrap();

        (vm, caller_private_key, credits, genesis)
    }

    /// Creates and verifies a mint_private transaction.
    fn mint_private<R: Rng + CryptoRng>(
        vm: &VM<CurrentNetwork, ConsensusMemory<CurrentNetwork>>,
        caller_private_key: &PrivateKey<CurrentNetwork>,
        recipient_view_key: &ViewKey<CurrentNetwork>,
        amount: u64,
        rng: &mut R,
    ) -> Result<Transaction<CurrentNetwork>> {
        // Derive the recipient keys.
        let recipient_address = Address::try_from(recipient_view_key)?;

        // Create a private mint transaction.
        let transaction = Transaction::execute(
            vm,
            caller_private_key,
            "credits.aleo",
            "mint_private",
            [Value::from_str(&recipient_address.to_string())?, Value::from_str(&format!("{amount}u64"))?].into_iter(),
            None,
            None,
            rng,
        )?;

        // Verify.
        assert!(vm.verify_transaction(&transaction));

        // Fetch the output records.
        let output_records = transaction.records().collect::<Vec<_>>();
        assert_eq!(output_records.len(), 1);

        // Check that the output record is correct.
        let (_, record) = output_records[0];
        let decrypted_record = record.decrypt(recipient_view_key)?;
        assert_eq!(***decrypted_record.gates(), amount);
        assert_eq!(**decrypted_record.owner(), recipient_address);

        Ok(transaction)
    }

    /// Creates and verifies a mint_public transaction.
    fn mint_public<R: Rng + CryptoRng>(
        vm: &VM<CurrentNetwork, ConsensusMemory<CurrentNetwork>>,
        caller_private_key: &PrivateKey<CurrentNetwork>,
        recipient_address: &Address<CurrentNetwork>,
        amount: u64,
        rng: &mut R,
    ) -> Result<Transaction<CurrentNetwork>> {
        // Create a public mint transaction.
        let transaction = Transaction::execute(
            vm,
            caller_private_key,
            "credits.aleo",
            "mint_public",
            [Value::from_str(&recipient_address.to_string())?, Value::from_str(&format!("{amount}u64"))?].into_iter(),
            None,
            None,
            rng,
        )?;

        // Verify.
        assert!(vm.verify_transaction(&transaction));

        // Check that there is no output record.
        let output_records = transaction.records().collect::<Vec<_>>();
        assert_eq!(output_records.len(), 0);

        // Verify the finalize state of the transaction.
        let transitions = transaction.transitions().collect::<Vec<_>>();
        assert_eq!(transitions.len(), 1);
        let values = transitions[0].finalize().unwrap();
        assert_eq!(values.len(), 2);
        assert_eq!(values[0].to_string(), recipient_address.to_string());
        assert_eq!(values[1].to_string(), format!("{amount}u64"));

        Ok(transaction)
    }

    /// Creates and verifies a transfer_private transaction.
    fn transfer_private<R: Rng + CryptoRng>(
        vm: &VM<CurrentNetwork, ConsensusMemory<CurrentNetwork>>,
        caller_private_key: &PrivateKey<CurrentNetwork>,
        credits: Record<CurrentNetwork, Plaintext<CurrentNetwork>>,
        recipient_view_key: &ViewKey<CurrentNetwork>,
        amount: u64,
        rng: &mut R,
    ) -> Result<Transaction<CurrentNetwork>> {
        // Derive the caller keys.
        let caller_view_key = ViewKey::try_from(caller_private_key)?;
        let caller_address = Address::try_from(caller_private_key)?;

        // Derive the recipient address.
        let recipient_address = Address::try_from(recipient_view_key)?;

        // Create a private mint transaction.
        let transaction = Transaction::execute(
            vm,
            caller_private_key,
            "credits.aleo",
            "transfer_private",
            [
                Value::Record(credits.clone()),
                Value::from_str(&recipient_address.to_string())?,
                Value::from_str(&format!("{amount}u64"))?,
            ]
            .into_iter(),
            None,
            None,
            rng,
        )?;

        // Verify.
        assert!(vm.verify_transaction(&transaction));

        // Fetch the output records.
        let output_records = transaction.records().collect::<Vec<_>>();
        assert_eq!(output_records.len(), 2);

        // Check that the output records are correct.
        let (_, record) = output_records[0];
        let decrypted_record = record.decrypt(recipient_view_key)?;
        assert_eq!(***decrypted_record.gates(), amount);
        assert_eq!(**decrypted_record.owner(), recipient_address);

        // Check that the change record is correct.
        let (_, record) = output_records[1];
        let decrypted_record = record.decrypt(&caller_view_key)?;
        assert_eq!(***decrypted_record.gates(), ***credits.gates() - amount);
        assert_eq!(**decrypted_record.owner(), caller_address);

        Ok(transaction)
    }

    /// Creates and verifies a transfer_private_to_public transaction.
    fn transfer_private_to_public<R: Rng + CryptoRng>(
        vm: &VM<CurrentNetwork, ConsensusMemory<CurrentNetwork>>,
        caller_private_key: &PrivateKey<CurrentNetwork>,
        credits: Record<CurrentNetwork, Plaintext<CurrentNetwork>>,
        recipient_address: &Address<CurrentNetwork>,
        amount: u64,
        rng: &mut R,
    ) -> Result<Transaction<CurrentNetwork>> {
        // Derive the caller keys.
        let caller_view_key = ViewKey::try_from(caller_private_key)?;
        let caller_address = Address::try_from(caller_private_key)?;

        // Create a private mint transaction.
        let transaction = Transaction::execute(
            vm,
            caller_private_key,
            "credits.aleo",
            "transfer_private_to_public",
            [
                Value::Record(credits.clone()),
                Value::from_str(&recipient_address.to_string())?,
                Value::from_str(&format!("{amount}u64"))?,
            ]
            .into_iter(),
            None,
            None,
            rng,
        )?;

        // Verify.
        assert!(vm.verify_transaction(&transaction));

        // Fetch the output records.
        let output_records = transaction.records().collect::<Vec<_>>();
        assert_eq!(output_records.len(), 1);

        // Check that the output record is correct.
        let (_, record) = output_records[0];
        let decrypted_record = record.decrypt(&caller_view_key)?;
        assert_eq!(***decrypted_record.gates(), ***credits.gates() - amount);
        assert_eq!(**decrypted_record.owner(), caller_address);

        // Verify the finalize state of the transaction.
        let transitions = transaction.transitions().collect::<Vec<_>>();
        assert_eq!(transitions.len(), 1);
        let values = transitions[0].finalize().unwrap();
        assert_eq!(values.len(), 2);
        assert_eq!(values[0].to_string(), recipient_address.to_string());
        assert_eq!(values[1].to_string(), format!("{amount}u64"));

        Ok(transaction)
    }

    /// Creates and verifies a transfer_public_to_private transaction.
    fn transfer_public_to_private<R: Rng + CryptoRng>(
        vm: &VM<CurrentNetwork, ConsensusMemory<CurrentNetwork>>,
        caller_private_key: &PrivateKey<CurrentNetwork>,
        recipient_view_key: &ViewKey<CurrentNetwork>,
        amount: u64,
        rng: &mut R,
    ) -> Result<Transaction<CurrentNetwork>> {
        // Derive the caller address.
        let caller_address = Address::try_from(caller_private_key)?;

        // Derive the recipient address.
        let recipient_address = Address::try_from(recipient_view_key)?;

        // Create a private mint transaction.
        let transaction = Transaction::execute(
            vm,
            caller_private_key,
            "credits.aleo",
            "transfer_public_to_private",
            [Value::from_str(&recipient_address.to_string())?, Value::from_str(&format!("{amount}u64"))?].into_iter(),
            None,
            None,
            rng,
        )?;

        // Verify.
        assert!(vm.verify_transaction(&transaction));

        // Fetch the output records.
        let output_records = transaction.records().collect::<Vec<_>>();
        assert_eq!(output_records.len(), 1);

        // Check that the output record is correct.
        let (_, record) = output_records[0];
        let decrypted_record = record.decrypt(recipient_view_key)?;
        assert_eq!(***decrypted_record.gates(), amount);
        assert_eq!(**decrypted_record.owner(), recipient_address);

        // Verify the finalize state of the transaction.
        let transitions = transaction.transitions().collect::<Vec<_>>();
        assert_eq!(transitions.len(), 1);
        let values = transitions[0].finalize().unwrap();
        assert_eq!(values.len(), 2);
        assert_eq!(values[0].to_string(), caller_address.to_string());
        assert_eq!(values[1].to_string(), format!("{amount}u64"));

        Ok(transaction)
    }

    /// Creates and verifies a transfer_public transaction.
    fn transfer_public<R: Rng + CryptoRng>(
        vm: &VM<CurrentNetwork, ConsensusMemory<CurrentNetwork>>,
        caller_private_key: &PrivateKey<CurrentNetwork>,
        recipient_address: &Address<CurrentNetwork>,
        amount: u64,
        rng: &mut R,
    ) -> Result<Transaction<CurrentNetwork>> {
        // Derive the caller address.
        let caller_address = Address::try_from(caller_private_key)?;

        // Create a private mint transaction.
        let transaction = Transaction::execute(
            vm,
            caller_private_key,
            "credits.aleo",
            "transfer_public",
            [Value::from_str(&recipient_address.to_string())?, Value::from_str(&format!("{amount}u64"))?].into_iter(),
            None,
            None,
            rng,
        )?;

        // Verify.
        assert!(vm.verify_transaction(&transaction));

        // Fetch the output records.
        let output_records = transaction.records().collect::<Vec<_>>();
        assert_eq!(output_records.len(), 0);

        // Verify the finalize state of the transaction.
        let transitions = transaction.transitions().collect::<Vec<_>>();
        assert_eq!(transitions.len(), 1);
        let values = transitions[0].finalize().unwrap();
        assert_eq!(values.len(), 3);
        assert_eq!(values[0].to_string(), caller_address.to_string());
        assert_eq!(values[1].to_string(), recipient_address.to_string());
        assert_eq!(values[2].to_string(), format!("{amount}u64"));

        Ok(transaction)
    }

    /// Creates and verifies a split transaction.
    fn split<R: Rng + CryptoRng>(
        vm: &VM<CurrentNetwork, ConsensusMemory<CurrentNetwork>>,
        caller_private_key: &PrivateKey<CurrentNetwork>,
        credits: Record<CurrentNetwork, Plaintext<CurrentNetwork>>,
        amount: u64,
        rng: &mut R,
    ) -> Result<Transaction<CurrentNetwork>> {
        // Derive the caller keys.
        let caller_view_key = ViewKey::try_from(caller_private_key)?;
        let caller_address = Address::try_from(caller_private_key)?;

        // Create a split transaction.
        let transaction = Transaction::execute(
            vm,
            caller_private_key,
            "credits.aleo",
            "split",
            [Value::Record(credits.clone()), Value::from_str(&format!("{amount}u64"))?].into_iter(),
            None,
            None,
            rng,
        )?;

        // Verify.
        assert!(vm.verify_transaction(&transaction));

        // Fetch the output records.
        let output_records = transaction.records().collect::<Vec<_>>();
        assert_eq!(output_records.len(), 2);

        // Check that the output records are correct.
        let (_, record) = output_records[0];
        let decrypted_record = record.decrypt(&caller_view_key)?;
        assert_eq!(***decrypted_record.gates(), amount);
        assert_eq!(**decrypted_record.owner(), caller_address);

        let (_, record) = output_records[1];
        let decrypted_record = record.decrypt(&caller_view_key)?;
        assert_eq!(***decrypted_record.gates(), ***credits.gates() - amount);
        assert_eq!(**decrypted_record.owner(), caller_address);

        Ok(transaction)
    }

    // Tests for `mint_private`

    #[test]
    fn test_mint_private() {
        let rng = &mut TestRng::default();

        // Sample a VM, caller, and genesis block.
        let (vm, caller_private_key, _, genesis) = initialize_state();

        // Create a recipient.
        let recipient_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
        let recipient_view_key = ViewKey::try_from(recipient_private_key).unwrap();

        // Create a private mint transaction.
        let amount = 1000u64;
        let transaction = mint_private(&vm, &caller_private_key, &recipient_view_key, amount, rng).unwrap();

        // Construct a new block for the private mint.
        let block = sample_next_block(&vm, &caller_private_key, &[transaction], &genesis, rng).unwrap();

        // Add the block.
        assert!(vm.add_next_block(&block).is_ok());
    }

    // Tests for `mint_public`

    #[test]
    fn test_mint_public() {
        let rng = &mut TestRng::default();

        // Sample a VM, caller, and genesis block.
        let (vm, caller_private_key, _, genesis) = initialize_state();

        // Create a recipient.
        let recipient_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
        let recipient_address = Address::try_from(recipient_private_key).unwrap();

        // Create a public mint transaction.
        let amount = 1000u64;
        let transaction = mint_public(&vm, &caller_private_key, &recipient_address, amount, rng).unwrap();

        // Construct a new block for the public mint.
        let block = sample_next_block(&vm, &caller_private_key, &[transaction], &genesis, rng).unwrap();

        // Add the block.
        assert!(vm.add_next_block(&block).is_ok());

        // Check the balances.
        let program_id = ProgramID::from_str("credits.aleo").unwrap();
        let mapping_name = Identifier::from_str("account").unwrap();
        let public_amount = vm
            .program_store()
            .get_value(&program_id, &mapping_name, &Plaintext::from(Literal::Address(recipient_address)))
            .unwrap();
        assert_eq!(public_amount.unwrap().to_string(), format!("{amount}u64"));
    }

    #[test]
    fn test_mint_public_existing_balance() {
        let rng = &mut TestRng::default();

        // Sample a VM, caller, and genesis block.
        let (vm, caller_private_key, _, genesis) = initialize_state();

        // Create a recipient.
        let recipient_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
        let recipient_address = Address::try_from(recipient_private_key).unwrap();

        // Create a public mint transaction.
        let amount_1 = 1000u64;
        let transaction = mint_public(&vm, &caller_private_key, &recipient_address, amount_1, rng).unwrap();

        // Construct a new block for the public mint.
        let block_1 = sample_next_block(&vm, &caller_private_key, &[transaction], &genesis, rng).unwrap();

        // Add the block.
        assert!(vm.add_next_block(&block_1).is_ok());

        // Check the balances.
        let program_id = ProgramID::from_str("credits.aleo").unwrap();
        let mapping_name = Identifier::from_str("account").unwrap();
        let public_amount = vm
            .program_store()
            .get_value(&program_id, &mapping_name, &Plaintext::from(Literal::Address(recipient_address)))
            .unwrap();
        assert_eq!(public_amount.unwrap().to_string(), format!("{amount_1}u64"));

        // Create another public mint transaction.
        let amount_2 = 1234u64;
        let transaction = mint_public(&vm, &caller_private_key, &recipient_address, amount_2, rng).unwrap();

        // Construct a new block for the public mint.
        let block_2 = sample_next_block(&vm, &caller_private_key, &[transaction], &block_1, rng).unwrap();

        // Add the block.
        assert!(vm.add_next_block(&block_2).is_ok());

        // Check the balances.
        let program_id = ProgramID::from_str("credits.aleo").unwrap();
        let mapping_name = Identifier::from_str("account").unwrap();
        let public_amount = vm
            .program_store()
            .get_value(&program_id, &mapping_name, &Plaintext::from(Literal::Address(recipient_address)))
            .unwrap();
        assert_eq!(public_amount.unwrap().to_string(), format!("{}u64", amount_1 + amount_2));
    }

    #[test]
    #[should_panic]
    fn test_mint_public_overflow() {
        let rng = &mut TestRng::default();

        // Sample a VM, caller, and genesis block.
        let (vm, caller_private_key, _, genesis) = initialize_state();

        // Derive caller address.
        let caller_address = Address::try_from(caller_private_key).unwrap();

        // Create a public mint transaction.
        let amount = u64::MAX;
        let transaction = mint_public(&vm, &caller_private_key, &caller_address, amount, rng).unwrap();

        // Construct a new block for the public mint.
        let block_1 = sample_next_block(&vm, &caller_private_key, &[transaction], &genesis, rng).unwrap();

        // Add the block.
        assert!(vm.add_next_block(&block_1).is_ok());

        // Create another public mint transaction that will cause an overflow.
        let amount = 10u64;
        let transaction = mint_public(&vm, &caller_private_key, &caller_address, amount, rng).unwrap();

        // Construct a new block with the overflow transaction.
        let block_2 = sample_next_block(&vm, &caller_private_key, &[transaction], &block_1, rng).unwrap();

        // Attempt to add the block. This should panic due to an overflow.
        assert!(vm.add_next_block(&block_2).is_err());
    }

    #[test]
    fn test_mint_public_accumulation_overflow() {
        let rng = &mut TestRng::default();

        // Sample a VM, caller, and genesis block.
        let (vm, caller_private_key, _, genesis) = initialize_state();

        // Derive the caller address.
        let caller_address = Address::try_from(caller_private_key).unwrap();

        // Create a public mint transaction.
        let amount_1 = u64::MAX;
        let transaction_1 = mint_public(&vm, &caller_private_key, &caller_address, amount_1, rng).unwrap();

        // Create another public mint transaction.
        let amount_2 = 1u64;
        let transaction_2 = mint_public(&vm, &caller_private_key, &caller_address, amount_2, rng).unwrap();

        let block =
            sample_next_block(&vm, &caller_private_key, &[transaction_1, transaction_2], &genesis, rng).unwrap();

        // Attempt to add the block. This should panic due to an overflow.
        assert!(vm.add_next_block(&block).is_err());
    }

    // Tests for `transfer_private`

    #[test]
    fn test_transfer_private() {
        let rng = &mut TestRng::default();

        // Sample a VM, caller, and genesis block.
        let (vm, caller_private_key, credits, genesis) = initialize_state();

        // Create a recipient.
        let recipient_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
        let recipient_view_key = ViewKey::try_from(&recipient_private_key).unwrap();

        // Create a private transfer transaction.
        let amount = 1000u64;
        let transaction =
            transfer_private(&vm, &caller_private_key, credits, &recipient_view_key, amount, rng).unwrap();

        // Construct a new block for the private transfer.
        let block = sample_next_block(&vm, &caller_private_key, &[transaction], &genesis, rng).unwrap();

        // Add the block.
        assert!(vm.add_next_block(&block).is_ok());
    }

    #[test]
    #[should_panic]
    fn test_transfer_private_exceeds_balance() {
        let rng = &mut TestRng::default();

        // Sample a VM, caller, and genesis block.
        let (vm, caller_private_key, credits, _) = initialize_state();

        // Create a recipient.
        let recipient_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
        let recipient_view_key = ViewKey::try_from(&recipient_private_key).unwrap();

        // Create a private transfer transaction.
        let amount = ***credits.gates() + 1;
        // This should panic due to an insufficient balance.
        assert!(transfer_private(&vm, &caller_private_key, credits, &recipient_view_key, amount, rng).is_err());
    }

    // Tests for `transfer_private_to_public`

    #[test]
    fn test_transfer_private_to_public() {
        let rng = &mut TestRng::default();

        // Sample a VM, caller, and genesis block.
        let (vm, caller_private_key, credits, genesis) = initialize_state();

        // Create a recipient.
        let recipient_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
        let recipient_address = Address::try_from(&recipient_private_key).unwrap();

        // Create a private transfer transaction.
        let amount = 1000u64;
        let transaction =
            transfer_private_to_public(&vm, &caller_private_key, credits, &recipient_address, amount, rng).unwrap();

        // Construct a new block for the private transfer.
        let block = sample_next_block(&vm, &caller_private_key, &[transaction], &genesis, rng).unwrap();

        // Add the block.
        assert!(vm.add_next_block(&block).is_ok());

        // Check the balances.
        let program_id = ProgramID::from_str("credits.aleo").unwrap();
        let mapping_name = Identifier::from_str("account").unwrap();
        let public_amount = vm
            .program_store()
            .get_value(&program_id, &mapping_name, &Plaintext::from(Literal::Address(recipient_address)))
            .unwrap();
        assert_eq!(public_amount.unwrap().to_string(), format!("{amount}u64"));
    }

    #[test]
    fn test_transfer_private_to_public_existing_balance() {
        let rng = &mut TestRng::default();

        // Sample a VM, caller, and genesis block.
        let (vm, caller_private_key, credits, genesis) = initialize_state();

        // Create a recipient.
        let recipient_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
        let recipient_address = Address::try_from(&recipient_private_key).unwrap();

        // Create a public mint transaction.
        let amount_1 = 1000u64;
        let transaction = mint_public(&vm, &caller_private_key, &recipient_address, amount_1, rng).unwrap();

        // Construct a new block for the public mint.
        let block_1 = sample_next_block(&vm, &caller_private_key, &[transaction], &genesis, rng).unwrap();

        // Add the block.
        assert!(vm.add_next_block(&block_1).is_ok());

        // Create a private transfer transaction.
        let amount_2 = 1000u64;
        let transaction =
            transfer_private_to_public(&vm, &caller_private_key, credits, &recipient_address, amount_2, rng).unwrap();

        // Construct a new block for the private transfer.
        let block_2 = sample_next_block(&vm, &caller_private_key, &[transaction], &block_1, rng).unwrap();

        // Add the block.
        assert!(vm.add_next_block(&block_2).is_ok());

        // Check the balances.
        let program_id = ProgramID::from_str("credits.aleo").unwrap();
        let mapping_name = Identifier::from_str("account").unwrap();
        let public_amount = vm
            .program_store()
            .get_value(&program_id, &mapping_name, &Plaintext::from(Literal::Address(recipient_address)))
            .unwrap();
        assert_eq!(public_amount.unwrap().to_string(), format!("{}u64", amount_1 + amount_2));
    }

    #[test]
    #[should_panic]
    fn test_transfer_private_to_public_exceeds_balance() {
        let rng = &mut TestRng::default();

        // Sample a VM, caller, and genesis block.
        let (vm, caller_private_key, credits, _) = initialize_state();

        // Create a recipient.
        let recipient_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
        let recipient_address = Address::try_from(&recipient_private_key).unwrap();

        // Create a private transfer transaction.
        let amount = ***credits.gates() + 1;
        // This should panic due to an insufficient balance.
        assert!(
            transfer_private_to_public(&vm, &caller_private_key, credits, &recipient_address, amount, rng).is_err()
        );
    }

    #[test]
    #[should_panic]
    fn test_transfer_private_to_public_overflow() {
        let rng = &mut TestRng::default();

        // Sample a VM, caller, and genesis block.
        let (vm, caller_private_key, credits, genesis) = initialize_state();

        // Derive caller address.
        let caller_address = Address::try_from(caller_private_key).unwrap();

        // Create a public mint transaction.
        let amount_1 = u64::MAX;
        let transaction = mint_public(&vm, &caller_private_key, &caller_address, amount_1, rng).unwrap();

        // Construct a new block for the public mint.
        let block_1 = sample_next_block(&vm, &caller_private_key, &[transaction], &genesis, rng).unwrap();

        // Add the block.
        assert!(vm.add_next_block(&block_1).is_ok());

        // Create another public mint transaction that will cause an overflow.
        let amount_2 = 10u64;
        let overflow_transaction =
            transfer_private_to_public(&vm, &caller_private_key, credits, &caller_address, amount_2, rng).unwrap();

        // Construct a new block with the overflow transaction.
        let block_2 = sample_next_block(&vm, &caller_private_key, &[overflow_transaction], &block_1, rng).unwrap();

        // Attempt to add the block. This should panic due to an overflow.
        assert!(vm.add_next_block(&block_2).is_err());
    }

    // Tests for `transfer_public_to_private`

    #[test]
    fn test_transfer_public_to_private() {
        let rng = &mut TestRng::default();

        // Sample a VM, caller, and genesis block.
        let (vm, caller_private_key, _, genesis) = initialize_state();

        // Derive the caller keys.
        let caller_address = Address::try_from(caller_private_key).unwrap();

        // Create a public mint transaction.
        let amount_1 = 2000u64;
        let transaction = mint_public(&vm, &caller_private_key, &caller_address, amount_1, rng).unwrap();

        // Construct a new block for the public mint.
        let block_1 = sample_next_block(&vm, &caller_private_key, &[transaction], &genesis, rng).unwrap();

        // Add the block.
        assert!(vm.add_next_block(&block_1).is_ok());

        // Create a recipient.
        let recipient_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
        let recipient_view_key = ViewKey::try_from(recipient_private_key).unwrap();

        // Create a public to private transfer transaction.
        let amount_2 = 1234u64;
        let transaction =
            transfer_public_to_private(&vm, &caller_private_key, &recipient_view_key, amount_2, rng).unwrap();

        // Construct a new block for the public to private transfer.
        let block_2 = sample_next_block(&vm, &caller_private_key, &[transaction], &block_1, rng).unwrap();

        // Add the block.
        assert!(vm.add_next_block(&block_2).is_ok());

        // Check the balances.
        let program_id = ProgramID::from_str("credits.aleo").unwrap();
        let mapping_name = Identifier::from_str("account").unwrap();
        let public_amount = vm
            .program_store()
            .get_value(&program_id, &mapping_name, &Plaintext::from(Literal::Address(caller_address)))
            .unwrap();
        assert_eq!(public_amount.unwrap().to_string(), format!("{}u64", amount_1 - amount_2));
    }

    #[test]
    fn test_transfer_public_to_private_exceeds_balance() {
        let rng = &mut TestRng::default();

        // Sample a VM, caller, and genesis block.
        let (vm, caller_private_key, _, genesis) = initialize_state();

        // Derive the caller keys.
        let caller_address = Address::try_from(caller_private_key).unwrap();

        // Create a public mint transaction.
        let amount_1 = 2000u64;
        let transaction = mint_public(&vm, &caller_private_key, &caller_address, amount_1, rng).unwrap();

        // Construct a new block for the public mint.
        let block_1 = sample_next_block(&vm, &caller_private_key, &[transaction], &genesis, rng).unwrap();

        // Add the block.
        assert!(vm.add_next_block(&block_1).is_ok());

        // Create a recipient.
        let recipient_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
        let recipient_view_key = ViewKey::try_from(recipient_private_key).unwrap();

        // Create a public to private transfer transaction using an amount that exceeds the balance.
        let amount_2 = amount_1 + 1;
        let transaction =
            transfer_public_to_private(&vm, &caller_private_key, &recipient_view_key, amount_2, rng).unwrap();

        // Construct a new block for the public to private transfer.
        let block_2 = sample_next_block(&vm, &caller_private_key, &[transaction], &block_1, rng).unwrap();

        // Attempt to add the block. This should panic due to insufficient funds.
        assert!(vm.add_next_block(&block_2).is_err());
    }

    // Tests for `transfer_public`

    #[test]
    fn test_transfer_public() {
        let rng = &mut TestRng::default();

        // Sample a VM, caller, and genesis block.
        let (vm, caller_private_key, _, genesis) = initialize_state();

        // Derive the caller address.
        let caller_address = Address::try_from(caller_private_key).unwrap();

        // Create a public mint transaction.
        let amount_1 = 2000u64;
        let transaction = mint_public(&vm, &caller_private_key, &caller_address, amount_1, rng).unwrap();

        // Construct a new block for the public mint.
        let block_1 = sample_next_block(&vm, &caller_private_key, &[transaction], &genesis, rng).unwrap();

        // Add the block.
        assert!(vm.add_next_block(&block_1).is_ok());

        // Create a recipient.
        let recipient_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
        let recipient_address = Address::try_from(recipient_private_key).unwrap();

        // Create a public transfer transaction.
        let amount_2 = 1234u64;
        let transaction = transfer_public(&vm, &caller_private_key, &recipient_address, amount_2, rng).unwrap();

        // Construct a new block for the public transfer.
        let block_2 = sample_next_block(&vm, &caller_private_key, &[transaction], &block_1, rng).unwrap();

        // Add the block.
        assert!(vm.add_next_block(&block_2).is_ok());

        // Check the balances.
        let program_id = ProgramID::from_str("credits.aleo").unwrap();
        let mapping_name = Identifier::from_str("account").unwrap();
        let caller_public_amount = vm
            .program_store()
            .get_value(&program_id, &mapping_name, &Plaintext::from(Literal::Address(caller_address)))
            .unwrap();
        assert_eq!(caller_public_amount.unwrap().to_string(), format!("{}u64", amount_1 - amount_2));

        let recipient_public_amount = vm
            .program_store()
            .get_value(&program_id, &mapping_name, &Plaintext::from(Literal::Address(recipient_address)))
            .unwrap();
        assert_eq!(recipient_public_amount.unwrap().to_string(), format!("{}u64", amount_2));
    }

    #[test]
    fn test_transfer_public_existing_balance() {
        let rng = &mut TestRng::default();

        // Sample a VM, caller, and genesis block.
        let (vm, caller_private_key, _, genesis) = initialize_state();

        // Derive the caller address.
        let caller_address = Address::try_from(caller_private_key).unwrap();

        // Create a public mint transaction.
        let amount_1 = 3000u64;
        let transaction = mint_public(&vm, &caller_private_key, &caller_address, amount_1, rng).unwrap();

        // Construct a new block for the public mint.
        let block_1 = sample_next_block(&vm, &caller_private_key, &[transaction], &genesis, rng).unwrap();

        // Add the block.
        assert!(vm.add_next_block(&block_1).is_ok());

        // Create a recipient.
        let recipient_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
        let recipient_address = Address::try_from(recipient_private_key).unwrap();

        // Create a public transfer transaction.
        let amount_2 = 1000u64;
        let transaction = transfer_public(&vm, &caller_private_key, &recipient_address, amount_2, rng).unwrap();

        // Construct a new block for the public transfer.
        let block_2 = sample_next_block(&vm, &caller_private_key, &[transaction], &block_1, rng).unwrap();

        // Add the block.
        assert!(vm.add_next_block(&block_2).is_ok());

        // Create another public transfer transaction.
        let amount_3 = 1000u64;
        let transaction = transfer_public(&vm, &caller_private_key, &recipient_address, amount_3, rng).unwrap();

        // Construct a new block for the public transfer.
        let block_3 = sample_next_block(&vm, &caller_private_key, &[transaction], &block_2, rng).unwrap();

        // Add the block.
        assert!(vm.add_next_block(&block_3).is_ok());

        // Check the balances.
        let program_id = ProgramID::from_str("credits.aleo").unwrap();
        let mapping_name = Identifier::from_str("account").unwrap();
        let caller_public_amount = vm
            .program_store()
            .get_value(&program_id, &mapping_name, &Plaintext::from(Literal::Address(caller_address)))
            .unwrap();
        assert_eq!(caller_public_amount.unwrap().to_string(), format!("{}u64", amount_1 - amount_2 - amount_3));

        let recipient_public_amount = vm
            .program_store()
            .get_value(&program_id, &mapping_name, &Plaintext::from(Literal::Address(recipient_address)))
            .unwrap();
        assert_eq!(recipient_public_amount.unwrap().to_string(), format!("{}u64", amount_2 + amount_3));
    }

    #[test]
    #[should_panic]
    fn test_transfer_public_exceeds_balance() {
        let rng = &mut TestRng::default();

        // Sample a VM, caller, and genesis block.
        let (vm, caller_private_key, _, genesis) = initialize_state();

        // Derive the caller address.
        let caller_address = Address::try_from(caller_private_key).unwrap();

        // Create a public mint transaction.
        let amount_1 = 1000u64;
        let transaction = mint_public(&vm, &caller_private_key, &caller_address, amount_1, rng).unwrap();

        // Construct a new block for the public mint.
        let block_1 = sample_next_block(&vm, &caller_private_key, &[transaction], &genesis, rng).unwrap();

        // Add the block.
        assert!(vm.add_next_block(&block_1).is_ok());

        // Create a recipient.
        let recipient_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
        let recipient_address = Address::try_from(recipient_private_key).unwrap();

        // Create a public transfer transaction using an amount that exceeds the balance.
        let amount_2 = amount_1 + 1;
        let transaction = transfer_public(&vm, &caller_private_key, &recipient_address, amount_2, rng).unwrap();

        // Construct a new block for the public transfer.
        let block_2 = sample_next_block(&vm, &caller_private_key, &[transaction], &block_1, rng).unwrap();

        // Attempt to add the block. This should panic due to insufficient funds.
        assert!(vm.add_next_block(&block_2).is_err());
    }

    #[test]
    #[should_panic]
    fn test_transfer_public_overflow() {
        let rng = &mut TestRng::default();

        // Sample a VM, caller, and genesis block.
        let (vm, caller_private_key, _, genesis) = initialize_state();

        // Derive the caller address.
        let caller_address = Address::try_from(caller_private_key).unwrap();

        // Create a recipient.
        let recipient_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
        let recipient_address = Address::try_from(recipient_private_key).unwrap();

        // Create a public mint transaction.
        let amount_1 = u64::MAX;
        let transaction_1 = mint_public(&vm, &caller_private_key, &recipient_address, amount_1, rng).unwrap();

        // Create another public mint transaction.
        let amount_2 = 1u64;
        let transaction_2 = mint_public(&vm, &caller_private_key, &caller_address, amount_2, rng).unwrap();

        let block_1 =
            sample_next_block(&vm, &caller_private_key, &[transaction_1, transaction_2], &genesis, rng).unwrap();

        // Add the block.
        assert!(vm.add_next_block(&block_1).is_err());

        // Create a public transfer transaction that will cause an overflow.
        let transaction_3 = transfer_public(&vm, &caller_private_key, &recipient_address, amount_2, rng).unwrap();

        // Construct a new block for the public transfer.
        let block_2 = sample_next_block(&vm, &caller_private_key, &[transaction_3], &block_1, rng).unwrap();

        // Attempt to add the block. This should panic due to an overflow.
        assert!(vm.add_next_block(&block_2).is_err());
    }

    #[test]
    fn test_transfer_public_to_self() {
        let rng = &mut TestRng::default();

        // Sample a VM, caller, and genesis block.
        let (vm, caller_private_key, _, genesis) = initialize_state();

        // Derive the caller address.
        let caller_address = Address::try_from(caller_private_key).unwrap();

        // Create a public mint transaction.
        let amount_1 = rng.gen_range(1..100_000_000);
        let transaction = mint_public(&vm, &caller_private_key, &caller_address, amount_1, rng).unwrap();

        // Construct a new block for the public mint.
        let block_1 = sample_next_block(&vm, &caller_private_key, &[transaction], &genesis, rng).unwrap();

        // Add the block.
        assert!(vm.add_next_block(&block_1).is_ok());

        // Create a public transfer transaction.
        let amount_2 = rng.gen_range(1..amount_1);
        let transaction = transfer_public(&vm, &caller_private_key, &caller_address, amount_2, rng).unwrap();

        // Construct a new block for the public transfer.
        let block_2 = sample_next_block(&vm, &caller_private_key, &[transaction], &block_1, rng).unwrap();

        // Add the block.
        assert!(vm.add_next_block(&block_2).is_ok());

        // Check the balances.
        let program_id = ProgramID::from_str("credits.aleo").unwrap();
        let mapping_name = Identifier::from_str("account").unwrap();
        let caller_public_amount = vm
            .program_store()
            .get_value(&program_id, &mapping_name, &Plaintext::from(Literal::Address(caller_address)))
            .unwrap();
        // Ensure the balance stays the same.
        assert_eq!(caller_public_amount.unwrap().to_string(), format!("{}u64", amount_1));
    }

    // Tests for `split`

    #[test]
    fn test_split() {
        let rng = &mut TestRng::default();

        // Sample a VM, caller, and genesis block.
        let (vm, caller_private_key, credits, genesis) = initialize_state();

        // Create a split transaction.
        let amount = 1000u64;
        let transaction = split(&vm, &caller_private_key, credits, amount, rng).unwrap();

        // Construct a new block for the split.
        let block = sample_next_block(&vm, &caller_private_key, &[transaction], &genesis, rng).unwrap();

        // Add the block.
        assert!(vm.add_next_block(&block).is_ok());
    }

    #[test]
    #[should_panic]
    fn test_split_exceeds_balance() {
        let rng = &mut TestRng::default();

        // Sample a VM, caller, and genesis block.
        let (vm, caller_private_key, credits, _) = initialize_state();

        // Create a split transaction.
        let amount = ***credits.gates() + 1;
        // This should panic due to an insufficient balance.
        assert!(split(&vm, &caller_private_key, credits, amount, rng).is_err());
    }
}
