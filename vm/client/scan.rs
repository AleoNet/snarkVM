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

impl<N: Network> Client<N> {
    /// Scans the ledger for records that match the given view key.
    #[allow(clippy::type_complexity)]
    pub fn scan(
        &self,
        view_key: impl TryInto<ViewKey<N>>,
        block_heights: Range<u32>,
    ) -> Result<Vec<(Field<N>, Record<N, Ciphertext<N>>)>> {
        // Prepare the view key.
        let view_key = view_key.try_into().map_err(|_| anyhow!("Invalid view key"))?;
        // Compute the x-coordinate of the address.
        let address_x_coordinate = view_key.to_address().to_x_coordinate();

        // Prepare the starting block height, by rounding down to the nearest step of 50.
        let start_block_height = block_heights.start - (block_heights.start % 50);
        // Prepare the ending block height, by rounding up to the nearest step of 50.
        let end_block_height = block_heights.end + (50 - (block_heights.end % 50));

        // Initialize a vector for the records.
        let mut records = Vec::new();

        for start_height in (start_block_height..end_block_height).step_by(50) {
            let end_height = start_height + 50;

            // Prepare the URL.
            let url = format!("{}/testnet3/blocks/phase3/{start_height}.{end_height}.blocks", self.base_url);
            // Request the blocks.
            let blocks_bytes = match reqwest::blocking::get(&url) {
                Ok(response) => match response.bytes() {
                    Ok(bytes) => bytes,
                    Err(error) => {
                        bail!("Failed to parse blocks {start_height} (inclusive) to {end_height} (exclusive): {error}")
                    }
                },
                Err(error) => {
                    // TODO (howardwu): Check if this range exceeds the latest block height that has been cached.
                    bail!("Failed to fetch blocks from {url}: {error}")
                }
            };

            // Convert the blocks bytes into an iterator of records.
            let records_iter = match bincode::deserialize::<Vec<Block<N>>>(&blocks_bytes) {
                Ok(blocks) => blocks.into_iter().flat_map(|block| block.into_records()),
                Err(error) => {
                    bail!("Failed to deserialize {start_height} (inclusive) to {end_height} (exclusive): {error}")
                }
            };

            // Filter the records by the view key.
            records.extend(records_iter.filter_map(|(commitment, record)| {
                match record.is_owner_with_address_x_coordinate(&view_key, &address_x_coordinate) {
                    true => Some((commitment, record)),
                    false => None,
                }
            }));
        }

        Ok(records)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use core::str::FromStr;
    use std::convert::TryFrom;

    type N = crate::prelude::Testnet3;

    #[test]
    fn test_scan() {
        // Initialize the client.
        let client = Client::<N>::new("https://vm.aleo.org/api").unwrap();

        // Derive the view key.
        let private_key =
            PrivateKey::<N>::from_str("APrivateKey1zkp5fCUVzS9b7my34CdraHBF9XzB58xYiPzFJQvjhmvv7A8").unwrap();
        let view_key = ViewKey::<N>::try_from(&private_key).unwrap();

        // Scan the ledger at this range.
        let records = client.scan(private_key, 14200..14250).unwrap();
        assert_eq!(records.len(), 1);

        // Check the commitment.
        let (commitment, record) = records[0].clone();
        assert_eq!(
            commitment.to_string(),
            "310298409899964034200900546312426933043797406211272306332560156413249565239field"
        );

        // Decrypt the record.
        let record = record.decrypt(&view_key).unwrap();
        let expected = r"{
  owner: aleo18x0yenrkceapvt85e6aqw2v8hq37hpt4ew6k6cgum6xlpmaxt5xqwnkuja.private,
  gates: 1099999999999864u64.private,
  _nonce: 3859911413360468505092363429199432421222291175370483298628506550397056121761group.public
}";
        assert_eq!(record.to_string(), expected);
    }
}
