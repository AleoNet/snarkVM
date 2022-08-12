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

impl<N: Network, B: BlockStorage<N>> Ledger<N, B> {
    /// Returns the block for the given block height.
    pub fn get_block(&self, height: u32) -> Result<Block<N>> {
        // Retrieve the block hash.
        let block_hash = match self.blocks.get_block_hash(height)? {
            Some(block_hash) => block_hash,
            None => bail!("Block {height} does not exist in storage"),
        };
        // Retrieve the block.
        match self.blocks.get_block(&block_hash)? {
            Some(block) => Ok(block),
            None => bail!("Block {height} ('{block_hash}') does not exist in storage"),
        }
    }

    /// Returns the block hash for the given block height.
    pub fn get_hash(&self, height: u32) -> Result<N::BlockHash> {
        match self.blocks.get_block_hash(height)? {
            Some(block_hash) => Ok(block_hash),
            None => bail!("Missing block hash for block {height}"),
        }
    }

    /// Returns the previous block hash for the given block height.
    pub fn get_previous_hash(&self, height: u32) -> Result<N::BlockHash> {
        match self.blocks.get_previous_block_hash(height)? {
            Some(previous_hash) => Ok(previous_hash),
            None => bail!("Missing previous block hash for block {height}"),
        }
    }

    /// Returns the block header for the given block height.
    pub fn get_header(&self, height: u32) -> Result<Header<N>> {
        // Retrieve the block hash.
        let block_hash = match self.blocks.get_block_hash(height)? {
            Some(block_hash) => block_hash,
            None => bail!("Block {height} does not exist in storage"),
        };
        // Retrieve the block header.
        match self.blocks.get_block_header(&block_hash)? {
            Some(header) => Ok(header),
            None => bail!("Missing block header for block {height}"),
        }
    }

    /// Returns the block transactions for the given block height.
    pub fn get_transactions(&self, height: u32) -> Result<Transactions<N>> {
        // Retrieve the block hash.
        let block_hash = match self.blocks.get_block_hash(height)? {
            Some(block_hash) => block_hash,
            None => bail!("Block {height} does not exist in storage"),
        };
        // Retrieve the block transaction.
        match self.blocks.get_block_transactions(&block_hash)? {
            Some(transactions) => Ok(transactions),
            None => bail!("Missing block transactions for block {height}"),
        }
    }

    /// Returns the block signature for the given block height.
    pub fn get_signature(&self, height: u32) -> Result<Signature<N>> {
        // Retrieve the block hash.
        let block_hash = match self.blocks.get_block_hash(height)? {
            Some(block_hash) => block_hash,
            None => bail!("Block {height} does not exist in storage"),
        };
        // Retrieve the block transaction.
        match self.blocks.get_block_signature(&block_hash)? {
            Some(signature) => Ok(signature),
            None => bail!("Missing signature for block {height}"),
        }
    }

    /// Returns the records that belong to the given view key.
    pub fn find_records<'a>(
        &'a self,
        view_key: &'a ViewKey<N>,
        filter: RecordsFilter<N>,
    ) -> impl '_ + Iterator<Item = (Field<N>, Record<N, Plaintext<N>>)> {
        // Derive the address from the view key.
        let address = view_key.to_address();

        self.records().flat_map(move |cow| {
            // A helper method to derive the tag from the `sk_tag` and commitment.
            let tag =
                |sk_tag: Field<N>, commitment: Field<N>| -> Result<Field<N>> { N::hash_psd2(&[sk_tag, commitment]) };

            // A helper method to derive the serial number from the private key and commitment.
            let serial_number = |private_key: PrivateKey<N>, commitment: Field<N>| -> Result<Field<N>> {
                // Compute the generator `H` as `HashToGroup(commitment)`.
                let h = N::hash_to_group_psd2(&[N::serial_number_domain(), commitment])?;
                // Compute `gamma` as `sk_sig * H`.
                let gamma = h * private_key.sk_sig();
                // Compute `sn_nonce` as `Hash(COFACTOR * gamma)`.
                let sn_nonce =
                    N::hash_to_scalar_psd2(&[N::serial_number_domain(), gamma.mul_by_cofactor().to_x_coordinate()])?;
                // Compute `serial_number` as `Commit(commitment, sn_nonce)`.
                N::commit_bhp512(&(N::serial_number_domain(), commitment).to_bits_le(), &sn_nonce)
            };

            // Retrieve the commitment and record.
            let (commitment, record) = match cow {
                (Cow::Borrowed(commitment), record) => (*commitment, record),
                (Cow::Owned(commitment), record) => (commitment, record),
            };

            // Determine whether to decrypt this record (or not), based on the filter.
            let commitment = match filter {
                RecordsFilter::All => commitment,
                RecordsFilter::AllSpent(private_key) => {
                    // Derive the serial number.
                    match serial_number(private_key, commitment) {
                        // Determine if the record is spent.
                        Ok(serial_number) => match self.contains_serial_number(&serial_number) {
                            Ok(true) => commitment,
                            Ok(false) => return None,
                            Err(e) => {
                                warn!("Failed to check serial number '{serial_number}' in the ledger: {e}");
                                return None;
                            }
                        },
                        Err(e) => {
                            warn!("Failed to derive serial number for record '{commitment}': {e}");
                            return None;
                        }
                    }
                }
                RecordsFilter::AllUnspent(private_key) => {
                    // Derive the serial number.
                    match serial_number(private_key, commitment) {
                        // Determine if the record is spent.
                        Ok(serial_number) => match self.contains_serial_number(&serial_number) {
                            Ok(true) => return None,
                            Ok(false) => commitment,
                            Err(e) => {
                                warn!("Failed to check serial number '{serial_number}' in the ledger: {e}");
                                return None;
                            }
                        },
                        Err(e) => {
                            warn!("Failed to derive serial number for record '{commitment}': {e}");
                            return None;
                        }
                    }
                }
                RecordsFilter::Spent(graph_key) => {
                    // Compute the `sk_tag` from the graph key.
                    let sk_tag = graph_key.sk_tag().to_x_coordinate();
                    // Derive the serial number.
                    match tag(sk_tag, commitment) {
                        // Determine if the record is spent.
                        Ok(tag) => match self.contains_tag(&tag) {
                            Ok(true) => commitment,
                            Ok(false) => return None,
                            Err(e) => {
                                warn!("Failed to check tag '{tag}' in the ledger: {e}");
                                return None;
                            }
                        },
                        Err(e) => {
                            warn!("Failed to derive the tag for record '{commitment}': {e}");
                            return None;
                        }
                    }
                }
                RecordsFilter::Unspent(graph_key) => {
                    // Compute the `sk_tag` from the graph key.
                    let sk_tag = graph_key.sk_tag().to_x_coordinate();
                    // Derive the serial number.
                    match tag(sk_tag, commitment) {
                        // Determine if the record is spent.
                        Ok(tag) => match self.contains_tag(&tag) {
                            Ok(true) => return None,
                            Ok(false) => commitment,
                            Err(e) => {
                                warn!("Failed to check tag '{tag}' in the ledger: {e}");
                                return None;
                            }
                        },
                        Err(e) => {
                            warn!("Failed to derive the tag for record '{commitment}': {e}");
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
                        warn!("Failed to decrypt record: {e}");
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
