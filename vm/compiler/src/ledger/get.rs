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

use std::borrow::Cow;

impl<
    N: Network,
    PreviousHashesMap: for<'a> Map<'a, u32, N::BlockHash>,
    HeadersMap: for<'a> Map<'a, u32, Header<N>>,
    TransactionsMap: for<'a> Map<'a, u32, Transactions<N>>,
    SignatureMap: for<'a> Map<'a, u32, Signature<N>>,
    ProgramsMap: for<'a> Map<'a, ProgramID<N>, Deployment<N>>,
> Ledger<N, PreviousHashesMap, HeadersMap, TransactionsMap, SignatureMap, ProgramsMap>
{
    /// Returns the block for the given block height.
    pub fn get_block(&self, height: u32) -> Result<Block<N>> {
        Block::from(
            self.get_previous_hash(height)?,
            *self.get_header(height)?,
            self.get_transactions(height)?.into_owned(),
            *self.get_signature(height)?,
        )
    }

    /// Returns the block hash for the given block height.
    pub fn get_hash(&self, height: u32) -> Result<N::BlockHash> {
        match height.cmp(&self.current_height) {
            Ordering::Equal => Ok(self.current_hash),
            Ordering::Less => match self.previous_hashes.get(&(height + 1))? {
                Some(block_hash) => Ok(*block_hash),
                None => bail!("Missing block hash for block {height}"),
            },
            Ordering::Greater => bail!("Block {height} (given) is greater than the current height"),
        }
    }

    /// Returns the current height of the ledger.
    pub fn get_current_height(&self) -> u32 {
        self.current_height
    }

    /// Returns the current round of the ledger.
    pub fn get_current_round(&self) -> u64 {
        self.current_round
    }

    /// Returns the current round of the ledger.
    pub fn get_current_hash(&self) -> &N::BlockHash {
        &self.current_hash
    }

    /// Returns the previous block hash for the given block height.
    pub fn get_previous_hash(&self, height: u32) -> Result<N::BlockHash> {
        match self.previous_hashes.get(&height)? {
            Some(previous_hash) => Ok(*previous_hash),
            None => bail!("Missing previous block hash for block {height}"),
        }
    }

    /// Returns the block header for the given block height.
    pub fn get_header(&self, height: u32) -> Result<Cow<'_, Header<N>>> {
        match self.headers.get(&height)? {
            Some(header) => Ok(header),
            None => bail!("Missing block header for block {height}"),
        }
    }

    /// Returns the block transactions for the given block height.
    pub fn get_transactions(&self, height: u32) -> Result<Cow<'_, Transactions<N>>> {
        match self.transactions.get(&height)? {
            Some(transactions) => Ok(transactions),
            None => bail!("Missing block transactions for block {height}"),
        }
    }

    /// Returns the block signature for the given block height.
    pub fn get_signature(&self, height: u32) -> Result<Cow<'_, Signature<N>>> {
        match self.signatures.get(&height)? {
            Some(signature) => Ok(signature),
            None => bail!("Missing signature for block {height}"),
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
                                true => *commitment,
                                false => return None,
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
                                true => return None,
                                false => *commitment,
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ledger::test_helpers::CurrentLedger;

    #[test]
    fn test_get_block() {
        // Load the genesis block.
        let genesis = Block::from_bytes_le(GenesisBytes::load_bytes()).unwrap();

        // Initialize a new ledger.
        let ledger = CurrentLedger::new().unwrap();
        // Retrieve the genesis block.
        let candidate = ledger.get_block(0).unwrap();
        // Ensure the genesis block matches.
        assert_eq!(genesis, candidate);
    }
}
