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

#[macro_use]
extern crate tracing;

mod helpers;
pub use helpers::*;

mod routes;
pub use routes::*;

use crate::{with, OrReject, RestError};

use snarkvm_compiler::{BlockStorage, Ledger, ProgramStorage, RecordsFilter, Transaction};
use snarkvm_console::{account::ViewKey, prelude::Network, types::Field};

use anyhow::Result;
use indexmap::IndexMap;
use parking_lot::RwLock;
use std::sync::Arc;
use tokio::{sync::mpsc, task::JoinHandle};
use warp::{http::StatusCode, reject, reply, Filter, Rejection, Reply};

/// Shorthand for the parent half of the `Ledger` message channel.
pub type LedgerSender<N> = mpsc::Sender<LedgerRequest<N>>;
/// Shorthand for the child half of the `Ledger` message channel.
pub type LedgerReceiver<N> = mpsc::Receiver<LedgerRequest<N>>;

/// An enum of requests that the `Ledger` struct processes.
#[derive(Debug)]
pub enum LedgerRequest<N: Network> {
    TransactionBroadcast(Transaction<N>),
}

/// A REST API server for the ledger.
pub struct Server<N: Network, B: BlockStorage<N>, P: ProgramStorage<N>> {
    /// The ledger.
    ledger: Arc<RwLock<Ledger<N, B, P>>>,
    /// The ledger sender.
    ledger_sender: LedgerSender<N>,
    /// The server handles.
    handles: Vec<JoinHandle<()>>,
}

impl<N: Network, B: 'static + BlockStorage<N>, P: 'static + ProgramStorage<N>> Server<N, B, P> {
    /// Initializes a new instance of the server.
    pub fn start(
        ledger: Arc<RwLock<Ledger<N, B, P>>>,
        additional_routes: Option<impl Filter<Extract = impl Reply, Error = Rejection> + Clone + Sync + Send + 'static>,
    ) -> Result<(Self, LedgerReceiver<N>)> {
        // Initialize a channel to send requests to the ledger.
        let (ledger_sender, ledger_receiver) = mpsc::channel(64);

        // Initialize the routes.
        let routes = Self::routes(ledger.clone(), ledger_sender.clone());

        // Initialize a vector for the server handles.
        let mut handles = Vec::new();

        // Spawn the server.
        handles.push(tokio::spawn(async move {
            // Initialize the listening IP.
            let ip = ([0, 0, 0, 0], 80);
            // Start the server, with optional additional routes.
            match additional_routes {
                Some(additional_routes) => warp::serve(routes.or(additional_routes)).run(ip).await,
                None => warp::serve(routes).run(ip).await,
            }
        }));

        // Initialize the server.
        let server = Self { ledger, ledger_sender, handles };

        Ok((server, ledger_receiver))
    }

    /// Initializes a ledger handler.
    pub fn start_handler(
        &mut self,
        ledger: Arc<RwLock<Ledger<N, B, P>>>,
        mut ledger_receiver: LedgerReceiver<N>,
    ) -> JoinHandle<()> {
        tokio::spawn(async move {
            while let Some(request) = ledger_receiver.recv().await {
                match request {
                    LedgerRequest::TransactionBroadcast(transaction) => {
                        let transaction_id = transaction.id();
                        match ledger.write().add_to_memory_pool(transaction) {
                            Ok(()) => trace!("✉️ Added transaction '{transaction_id}' to the memory pool"),
                            Err(error) => {
                                warn!("⚠️ Failed to add transaction '{transaction_id}' to the memory pool: {error}")
                            }
                        }
                    }
                };
            }
        })
    }

    /// Returns the ledger.
    pub fn ledger(&self) -> Arc<RwLock<Ledger<N, B, P>>> {
        self.ledger.clone()
    }

    /// Returns the ledger sender.
    pub fn ledger_sender(&self) -> &LedgerSender<N> {
        &self.ledger_sender
    }

    /// Returns the handles.
    pub fn handles(&self) -> &Vec<JoinHandle<()>> {
        &self.handles
    }
}
