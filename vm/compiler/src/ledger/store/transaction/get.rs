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

use crate::ledger::{OutputRecordsFilter, Plaintext, PrivateKey, Record, ViewKey};

use crate::Execution;
use core::borrow::Borrow;
use std::borrow::Cow;

impl<
    N: Network,
    DeploymentsMap: for<'a> Map<'a, N::TransactionID, (Deployment<N>, N::TransitionID)>,
    ExecutionsMap: for<'a> Map<'a, N::TransactionID, (Vec<N::TransitionID>, Option<N::TransitionID>)>,
    TransitionsMap: for<'a> Map<'a, N::TransitionID, Transition<N>>,
    TransitionPublicKeysMap: for<'a> Map<'a, Group<N>, N::TransitionID>,
    SerialNumbersMap: for<'a> Map<'a, Field<N>, N::TransitionID>,
    CommitmentsMap: for<'a> Map<'a, Field<N>, N::TransitionID>,
    OriginsMap: for<'a> Map<'a, Origin<N>, N::TransitionID>,
    NonceMap: for<'a> Map<'a, Group<N>, N::TransitionID>,
>
    TransactionStore<
        N,
        DeploymentsMap,
        ExecutionsMap,
        TransitionsMap,
        TransitionPublicKeysMap,
        SerialNumbersMap,
        CommitmentsMap,
        OriginsMap,
        NonceMap,
    >
{
    /// Returns the transaction for the given transaction id.
    pub fn get_transaction(&self, transaction_id: N::TransactionID) -> Result<Transaction<N>> {
        if let Some(value) = self.deployments.get(&transaction_id)? {
            // Return the deployment transaction.
            let (deployment, additional_fee) = value.borrow();
            Transaction::from_deployment(deployment.clone(), self.get_transition(*additional_fee)?.into_owned())
        } else if let Some(value) = self.executions.get(&transaction_id)? {
            // Return the execution transaction.
            let (execution, additional_fee) = value.borrow();

            let transitions: Result<Vec<_>> = execution
                .iter()
                .map(|transition_id| self.get_transition(*transition_id).map(|t| t.into_owned()))
                .collect();
            let execution = Execution::from(N::ID, &transitions?)?;
            let additional_fee = match additional_fee {
                Some(transition_id) => Some(self.get_transition(*transition_id)?.into_owned()),
                None => None,
            };

            Transaction::from_execution(execution, additional_fee)
        } else {
            bail!("Missing transaction with id {transaction_id}")
        }
    }

    /// Returns the transactions for the given transition id.
    pub fn get_transition(&self, transition_id: N::TransitionID) -> Result<Cow<'_, Transition<N>>> {
        match self.transitions.get(&transition_id)? {
            Some(transition) => Ok(transition),
            None => bail!("Missing transition with id {transition_id}"),
        }
    }

    // TODO (raychu86): Rename this.
    /// Returns the transactions for the given commitment.
    pub fn get_transition_id_from_commitment(&self, commitment: N::TransitionID) -> Result<Cow<'_, N::TransitionID>> {
        match self.commitments.get(&commitment)? {
            Some(transition_id) => Ok(transition_id),
            None => bail!("Missing commitment {commitment}"),
        }
    }

    /// Returns the output records that belong to the given view key.
    pub fn get_output_records<'a>(
        &'a self,
        view_key: &'a ViewKey<N>,
        filter: OutputRecordsFilter<N>,
    ) -> impl '_ + Iterator<Item = (Field<N>, Record<N, Plaintext<N>>)> {
        // Derive the address from the view key.
        let address = view_key.to_address();

        self.transitions()
            .flat_map(|ts| match ts {
                Cow::Borrowed(tn) => Transition::output_records(tn)
                    .map(|(f, r)| (Cow::Borrowed(f), Cow::Borrowed(r)))
                    .collect::<Vec<_>>(),
                Cow::Owned(tn) => Transition::output_records(&tn)
                    .map(|(f, r)| (Cow::Owned(f.to_owned()), Cow::Owned(r.to_owned())))
                    .collect::<Vec<_>>(),
            })
            .flat_map(move |(commitment, record)| {
                // A helper method to derive the serial number from the private key and commitment.
                let serial_number = |private_key: PrivateKey<N>, commitment: Field<N>| -> Result<Field<N>> {
                    // Compute the generator `H` as `HashToGroup(commitment)`.
                    let h = N::hash_to_group_psd2(&[N::serial_number_domain(), commitment])?;
                    // Compute `gamma` as `sk_sig * H`.
                    let gamma = h * private_key.sk_sig();
                    // Compute `sn_nonce` as `Hash(COFACTOR * gamma)`.
                    let sn_nonce = N::hash_to_scalar_psd2(&[
                        N::serial_number_domain(),
                        gamma.mul_by_cofactor().to_x_coordinate(),
                    ])?;
                    // Compute `serial_number` as `Commit(commitment, sn_nonce)`.
                    N::commit_bhp512(&(N::serial_number_domain(), commitment).to_bits_le(), &sn_nonce)
                };

                // Determine whether to decrypt this output record (or not), based on the filter.
                let commitment = match filter {
                    OutputRecordsFilter::All => *commitment,
                    OutputRecordsFilter::Spent(private_key) => {
                        // Derive the serial number.
                        match serial_number(private_key, *commitment) {
                            // Determine if the output record is spent.
                            Ok(serial_number) => match self.contains_serial_number(&serial_number) {
                                Ok(true) => *commitment,
                                _ => return None,
                            },
                            Err(e) => {
                                warn!("Failed to derive serial number for output record: {e}");
                                return None;
                            }
                        }
                    }
                    OutputRecordsFilter::Unspent(private_key) => {
                        // Derive the serial number.
                        match serial_number(private_key, *commitment) {
                            // Determine if the output record is spent.
                            Ok(serial_number) => match self.contains_serial_number(&serial_number) {
                                Ok(true) => return None,
                                _ => *commitment,
                            },
                            Err(e) => {
                                warn!("Failed to derive serial number for output record: {e}");
                                return None;
                            }
                        }
                    }
                };

                // Decrypt the record.
                match record.is_owner(&address, view_key) {
                    true => match record.decrypt(view_key) {
                        Ok(record) => Some((commitment, record)),
                        Err(e) => {
                            warn!("Failed to decrypt output record: {e}");
                            None
                        }
                    },
                    false => None,
                }
            })
    }
}
