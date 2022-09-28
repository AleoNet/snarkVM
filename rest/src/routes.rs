// Copyright (C) 2019-2022 Aleo Systems Inc.
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
use snarkvm_console::{
    account::PrivateKey,
    prelude::{de, Deserializer, Zero},
    program::{Identifier, Value},
};

use std::str::FromStr;

/// The `get_blocks` query object.
#[derive(Deserialize, Serialize)]
struct BlockRange {
    start: u32,
    end: u32,
}

struct TransferData<N: Network> {
    from: PrivateKey<N>,
    to: Address<N>,
    amount: u64,
}

impl<N: Network> TransferData<N> {
    fn new(from: PrivateKey<N>, to: Address<N>, amount: u64) -> Self {
        Self { from, to, amount }
    }
}

impl<'de, N: Network> Deserialize<'de> for TransferData<N> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let request = serde_json::Value::deserialize(deserializer)?;

        Ok(Self::new(
            serde_json::from_value(request["from"].clone()).map_err(de::Error::custom)?,
            serde_json::from_value(request["to"].clone()).map_err(de::Error::custom)?,
            serde_json::from_value(request["amount"].clone()).map_err(de::Error::custom)?,
        ))
    }
}

impl<N: Network, B: BlockStorage<N>, P: ProgramStorage<N>> Server<N, B, P> {
    /// Initializes the routes, given the ledger and ledger sender.
    #[allow(clippy::redundant_clone)]
    pub fn routes(&self) -> impl Filter<Extract = impl Reply, Error = Rejection> + Clone {
        // GET /testnet3/latest/height
        let latest_height = warp::get()
            .and(warp::path!("testnet3" / "latest" / "height"))
            .and(with(self.ledger.clone()))
            .and_then(Self::latest_height);

        // GET /testnet3/latest/hash
        let latest_hash = warp::get()
            .and(warp::path!("testnet3" / "latest" / "hash"))
            .and(with(self.ledger.clone()))
            .and_then(Self::latest_hash);

        // GET /testnet3/latest/block
        let latest_block = warp::get()
            .and(warp::path!("testnet3" / "latest" / "block"))
            .and(with(self.ledger.clone()))
            .and_then(Self::latest_block);

        // GET /testnet3/block/{height}
        let get_block = warp::get()
            .and(warp::path!("testnet3" / "block" / u32))
            .and(with(self.ledger.clone()))
            .and_then(Self::get_block);

        // GET /testnet3/block?start={start_height}&end={end_height}
        let get_blocks = warp::get()
            .and(warp::path!("testnet3" / "blocks"))
            .and(warp::query::<BlockRange>())
            .and(with(self.ledger.clone()))
            .and_then(Self::get_blocks);

        // GET /testnet3/transactions/{height}
        let get_transactions = warp::get()
            .and(warp::path!("testnet3" / "transactions" / u32))
            .and(with(self.ledger.clone()))
            .and_then(Self::get_transactions);

        // GET /testnet3/transaction/{id}
        let get_transaction = warp::get()
            .and(warp::path!("testnet3" / "transaction" / ..))
            .and(warp::path::param::<N::TransactionID>())
            .and(warp::path::end())
            .and(with(self.ledger.clone()))
            .and_then(Self::get_transaction);

        // GET /testnet3/transactions/mempool
        let get_transactions_mempool = warp::get()
            .and(warp::path!("testnet3" / "transactions" / "mempool"))
            .and(with(self.ledger.clone()))
            .and_then(Self::get_transactions_mempool);

        // GET /testnet3/program/{id}
        let get_program = warp::get()
            .and(warp::path!("testnet3" / "program" / ..))
            .and(warp::path::param::<ProgramID<N>>())
            .and(warp::path::end())
            .and(with(self.ledger.clone()))
            .and_then(Self::get_program);

        // GET /testnet3/validators
        let get_validators = warp::get()
            .and(warp::path!("testnet3" / "validators"))
            .and(with(self.ledger.clone()))
            .and_then(Self::get_validators);

        // POST /testnet3/statePath/{commitment}
        let get_state_path = warp::post()
            .and(warp::path!("testnet3" / "statePath"))
            .and(warp::body::content_length_limit(128))
            .and(warp::body::json())
            .and(with(self.ledger.clone()))
            .and_then(Self::get_state_path);

        // POST /testnet3/records/all
        let records_all = warp::post()
            .and(warp::path!("testnet3" / "records" / "all"))
            .and(warp::body::content_length_limit(128))
            .and(warp::body::json())
            .and(with(self.ledger.clone()))
            .and_then(Self::records_all);

        // POST /testnet3/records/spent
        let records_spent = warp::post()
            .and(warp::path!("testnet3" / "records" / "spent"))
            .and(warp::body::content_length_limit(128))
            .and(warp::body::json())
            .and(with(self.ledger.clone()))
            .and_then(Self::records_spent);

        // POST /testnet3/records/unspent
        let records_unspent = warp::post()
            .and(warp::path!("testnet3" / "records" / "unspent"))
            .and(warp::body::content_length_limit(128))
            .and(warp::body::json())
            .and(with(self.ledger.clone()))
            .and_then(Self::records_unspent);

        // POST /testnet3/ciphertexts/unspent
        let ciphertexts_unspent = warp::post()
            .and(warp::path!("testnet3" / "ciphertexts" / "unspent"))
            .and(warp::body::content_length_limit(128))
            .and(warp::body::json())
            .and(with(self.ledger.clone()))
            .and_then(Self::ciphertexts_unspent);

        // POST /testnet3/transaction/broadcast
        let transaction_broadcast = warp::post()
            .and(warp::path!("testnet3" / "transaction" / "broadcast"))
            .and(warp::body::content_length_limit(10 * 1024 * 1024))
            .and(warp::body::json())
            .and(with(self.ledger_sender.clone()))
            .and(with(self.ledger.clone()))
            .and_then(Self::transaction_broadcast);

        // POST /testnet3/transfer
        let create_transfer = warp::post()
            .and(warp::path!("testnet3" / "transfer"))
            .and(warp::body::content_length_limit(10 * 1024 * 1024))
            .and(warp::body::json())
            .and(with(self.ledger.clone()))
            .and(with(self.ledger_sender.clone()))
            .and_then(Self::create_transfer);

        // Return the list of routes.
        latest_height
            .or(latest_hash)
            .or(latest_block)
            .or(get_block)
            .or(get_blocks)
            .or(get_transactions)
            .or(get_transaction)
            .or(get_transactions_mempool)
            .or(get_program)
            .or(get_validators)
            .or(get_state_path)
            .or(records_all)
            .or(records_spent)
            .or(records_unspent)
            .or(ciphertexts_unspent)
            .or(transaction_broadcast)
            .or(create_transfer)
    }
}

impl<N: Network, B: BlockStorage<N>, P: ProgramStorage<N>> Server<N, B, P> {
    /// Returns the latest block height.
    async fn latest_height(ledger: Arc<RwLock<Ledger<N, B, P>>>) -> Result<impl Reply, Rejection> {
        Ok(reply::json(&ledger.read().latest_height()))
    }

    /// Returns the latest block hash.
    async fn latest_hash(ledger: Arc<RwLock<Ledger<N, B, P>>>) -> Result<impl Reply, Rejection> {
        Ok(reply::json(&ledger.read().latest_hash()))
    }

    /// Returns the latest block.
    async fn latest_block(ledger: Arc<RwLock<Ledger<N, B, P>>>) -> Result<impl Reply, Rejection> {
        Ok(reply::json(&ledger.read().latest_block().or_reject()?))
    }

    /// Returns the block for the given block height.
    async fn get_block(height: u32, ledger: Arc<RwLock<Ledger<N, B, P>>>) -> Result<impl Reply, Rejection> {
        Ok(reply::json(&ledger.read().get_block(height).or_reject()?))
    }

    /// Returns the blocks for the given block range.
    async fn get_blocks(
        block_range: BlockRange,
        ledger: Arc<RwLock<Ledger<N, B, P>>>,
    ) -> Result<impl Reply, Rejection> {
        let start_height = block_range.start;
        let end_height = block_range.end;

        // Ensure the end height is greater than the start height.
        if start_height > end_height {
            return Err(reject::custom(RestError::Request("Invalid block range".to_string())));
        }

        // Ensure the block range is bounded.
        const MAX_BLOCK_RANGE: u32 = 50;
        if end_height - start_height >= MAX_BLOCK_RANGE {
            return Err(reject::custom(RestError::Request(format!(
                "Too many blocks requested. Max 50, requested {}",
                end_height - start_height
            ))));
        }

        let blocks = (start_height..end_height)
            .map(|height| ledger.read().get_block(height).or_reject())
            .collect::<Result<Vec<_>, _>>()?;

        Ok(reply::json(&blocks))
    }

    /// Returns the transactions for the given block height.
    async fn get_transactions(height: u32, ledger: Arc<RwLock<Ledger<N, B, P>>>) -> Result<impl Reply, Rejection> {
        Ok(reply::json(&ledger.read().get_transactions(height).or_reject()?))
    }

    /// Returns the transaction for the given transaction ID.
    async fn get_transaction(
        transaction_id: N::TransactionID,
        ledger: Arc<RwLock<Ledger<N, B, P>>>,
    ) -> Result<impl Reply, Rejection> {
        Ok(reply::json(&ledger.read().get_transaction(transaction_id).or_reject()?))
    }

    /// Returns the transactions in the memory pool.
    async fn get_transactions_mempool(ledger: Arc<RwLock<Ledger<N, B, P>>>) -> Result<impl Reply, Rejection> {
        Ok(reply::json(&ledger.read().memory_pool().values().collect::<Vec<_>>()))
    }

    /// Returns the program for the given program ID.
    async fn get_program(
        program_id: ProgramID<N>,
        ledger: Arc<RwLock<Ledger<N, B, P>>>,
    ) -> Result<impl Reply, Rejection> {
        Ok(reply::json(&ledger.read().get_program(program_id).or_reject()?))
    }

    /// Returns the list of current validators.
    async fn get_validators(ledger: Arc<RwLock<Ledger<N, B, P>>>) -> Result<impl Reply, Rejection> {
        Ok(reply::json(&ledger.read().validators().keys().collect::<Vec<&Address<N>>>()))
    }

    /// Returns the state path for the given commitment.
    async fn get_state_path(
        commitment: Field<N>,
        ledger: Arc<RwLock<Ledger<N, B, P>>>,
    ) -> Result<impl Reply, Rejection> {
        Ok(reply::json(&ledger.read().to_state_path(&commitment).or_reject()?))
    }

    /// Returns all of the records for the given view key.
    async fn records_all(view_key: ViewKey<N>, ledger: Arc<RwLock<Ledger<N, B, P>>>) -> Result<impl Reply, Rejection> {
        // Fetch the records using the view key.
        let records: IndexMap<_, _> = ledger.read().find_records(&view_key, RecordsFilter::All).or_reject()?.collect();
        // Return the records.
        Ok(reply::with_status(reply::json(&records), StatusCode::OK))
    }

    /// Returns the spent records for the given view key.
    async fn records_spent(
        view_key: ViewKey<N>,
        ledger: Arc<RwLock<Ledger<N, B, P>>>,
    ) -> Result<impl Reply, Rejection> {
        // Fetch the records using the view key.
        let records =
            ledger.read().find_records(&view_key, RecordsFilter::Spent).or_reject()?.collect::<IndexMap<_, _>>();
        // Return the records.
        Ok(reply::with_status(reply::json(&records), StatusCode::OK))
    }

    /// Returns the unspent records for the given view key.
    async fn records_unspent(
        view_key: ViewKey<N>,
        ledger: Arc<RwLock<Ledger<N, B, P>>>,
    ) -> Result<impl Reply, Rejection> {
        // Fetch the records using the view key.
        let records = ledger
            .read()
            .find_records(&view_key, RecordsFilter::Unspent)
            .or_reject()?
            .map(|(_commitment, record)| record)
            .collect::<Vec<_>>();
        // Return the records.
        Ok(reply::with_status(reply::json(&records), StatusCode::OK))
    }

    /// Returns the unspent records for the given view key.
    async fn ciphertexts_unspent(
        view_key: ViewKey<N>,
        ledger: Arc<RwLock<Ledger<N, B, P>>>,
    ) -> Result<impl Reply, Rejection> {
        // Fetch the records using the view key.
        let ledger_reader = ledger.read();
        let records =
            ledger_reader.find_record_ciphertexts(&view_key, RecordsFilter::Unspent).or_reject()?.map(|(_commitment, record_ciphertext)| record_ciphertext).collect::<Vec<_>>();
        // Return the records.
        Ok(reply::with_status(reply::json(&records), StatusCode::OK))
    }

    /// Broadcasts the transaction to the ledger.
    async fn transaction_broadcast(
        transaction: Transaction<N>,
        ledger_sender: LedgerSender<N>,
        ledger: Arc<RwLock<Ledger<N, B, P>>>,
    ) -> Result<impl Reply, Rejection> {
        // Validate the transaction.
        ledger.read().check_transaction(&transaction).or_reject()?;

        // Send the transaction to the ledger.
        match ledger_sender.send(LedgerRequest::TransactionBroadcast(transaction)).await {
            Ok(()) => Ok("OK"),
            Err(error) => Err(reject::custom(RestError::Request(format!("{error}")))),
        }
    }

    /// Creates a transfer transaction.
    async fn create_transfer(
        query: TransferData<N>,
        ledger: Arc<RwLock<Ledger<N, B, P>>>,
        ledger_sender: LedgerSender<N>,
    ) -> Result<impl Reply, Rejection> {
        let from = query.from;
        let to = query.to;
        let amount = query.amount;
        let view_key = ViewKey::try_from(from).or_reject()?;

        // TODO: This solution introduces a race condition because the same
        // record could be found twice to use. Doing this the right way doesn't
        // work because RwLockReadGuard does not implement the Send trait and
        // thus cannot be sent between threads safely.

        let (_, max_credits_record) = ledger
            .read()
            .find_records(&view_key, RecordsFilter::Unspent)
            .or_reject()?
            .filter(|(_, record)| !record.gates().is_zero())
            .max_by(|(_, record_a), (_, record_b)| (**record_a.gates()).cmp(&**record_b.gates()))
            .or_reject()?;

        let transfer_transaction = Transaction::execute(
            ledger.read().vm(),
            &from,
            &ProgramID::from_str("credits.aleo").or_reject()?,
            Identifier::from_str("transfer").or_reject()?,
            &[
                Value::Record(max_credits_record),
                Value::from_str(&format!("{to}")).or_reject()?,
                Value::from_str(&format!("{amount}u64")).or_reject()?,
            ],
            None,
            &mut rand::thread_rng(),
        )
        .or_reject()?;

        match ledger_sender.send(LedgerRequest::TransactionBroadcast(transfer_transaction)).await {
            Ok(()) => Ok("OK"),
            Err(error) => Err(reject::custom(RestError::Request(format!("{error}")))),
        }
    }
}
