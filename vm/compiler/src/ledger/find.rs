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

impl<N: Network, B: BlockStorage<N>, P: ProgramStorage<N>> Ledger<N, B, P> {
    /// Returns the record ciphertexts that belong to the given view key.
    pub fn find_record_ciphertexts<'a>(
        &'a self,
        view_key: &'a ViewKey<N>,
        filter: RecordsFilter<N>,
    ) -> Result<impl '_ + Iterator<Item = (Field<N>, Cow<'_, Record<N, Ciphertext<N>>>)>> {
        // Derive the address from the view key.
        let address = view_key.to_address();
        // Derive the `sk_tag` from the graph key.
        let sk_tag = match GraphKey::try_from(view_key) {
            Ok(graph_key) => graph_key.sk_tag(),
            Err(e) => bail!("Failed to derive the graph key from the view key: {e}"),
        };

        /// A helper method to derive the tag from the `sk_tag` and commitment.
        fn compute_tag<N: Network>(sk_tag: Field<N>, commitment: Field<N>) -> Result<Field<N>> {
            N::hash_psd2(&[sk_tag, commitment])
        }

        /// A helper method to derive the serial number from the private key and commitment.
        fn compute_serial_number<N: Network>(private_key: PrivateKey<N>, commitment: Field<N>) -> Result<Field<N>> {
            // Compute the generator `H` as `HashToGroup(commitment)`.
            let h = N::hash_to_group_psd2(&[N::serial_number_domain(), commitment])?;
            // Compute `gamma` as `sk_sig * H`.
            let gamma = h * private_key.sk_sig();
            // Compute `sn_nonce` as `Hash(COFACTOR * gamma)`.
            let sn_nonce =
                N::hash_to_scalar_psd2(&[N::serial_number_domain(), gamma.mul_by_cofactor().to_x_coordinate()])?;
            // Compute `serial_number` as `Commit(commitment, sn_nonce)`.
            N::commit_bhp512(&(N::serial_number_domain(), commitment).to_bits_le(), &sn_nonce)
        }

        Ok(self.records().flat_map(move |cow| {
            // Retrieve the commitment and record.
            let (commitment, record) = match cow {
                (Cow::Borrowed(commitment), record) => (*commitment, record),
                (Cow::Owned(commitment), record) => (commitment, record),
            };

            // Determine whether to decrypt this record (or not), based on the filter.
            let commitment = match filter {
                RecordsFilter::All => Ok(Some(commitment)),
                RecordsFilter::Spent => compute_tag(sk_tag, commitment).and_then(|tag| {
                    // Determine if the record is spent.
                    self.contains_tag(&tag).map(|is_spent| match is_spent {
                        true => Some(commitment),
                        false => None,
                    })
                }),
                RecordsFilter::Unspent => compute_tag(sk_tag, commitment).and_then(|tag| {
                    // Determine if the record is spent.
                    self.contains_tag(&tag).map(|is_spent| match is_spent {
                        true => None,
                        false => Some(commitment),
                    })
                }),
                RecordsFilter::SlowSpent(private_key) => {
                    compute_serial_number(private_key, commitment).and_then(|serial_number| {
                        // Determine if the record is spent.
                        self.contains_serial_number(&serial_number).map(|is_spent| match is_spent {
                            true => Some(commitment),
                            false => None,
                        })
                    })
                }
                RecordsFilter::SlowUnspent(private_key) => {
                    compute_serial_number(private_key, commitment).and_then(|serial_number| {
                        // Determine if the record is spent.
                        self.contains_serial_number(&serial_number).map(|is_spent| match is_spent {
                            true => None,
                            false => Some(commitment),
                        })
                    })
                }
            };

            match commitment {
                Ok(Some(commitment)) => match record.is_owner(&address, view_key) {
                    true => Some((commitment, record)),
                    false => None,
                },
                Ok(None) => None,
                Err(e) => {
                    warn!("Failed to process 'find_record_ciphertexts({:?})': {e}", filter);
                    None
                }
            }
        }))
    }

    /// Returns the records that belong to the given view key.
    pub fn find_records<'a>(
        &'a self,
        view_key: &'a ViewKey<N>,
        filter: RecordsFilter<N>,
    ) -> Result<impl '_ + Iterator<Item = (Field<N>, Record<N, Plaintext<N>>)>> {
        self.find_record_ciphertexts(view_key, filter).map(|iter| {
            iter.flat_map(|(commitment, record)| match record.decrypt(view_key) {
                Ok(record) => Some((commitment, record)),
                Err(e) => {
                    warn!("Failed to decrypt the record: {e}");
                    None
                }
            })
        })
    }
}
