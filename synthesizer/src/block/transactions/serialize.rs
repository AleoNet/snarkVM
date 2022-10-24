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

impl<N: Network> Serialize for Transactions<N> {
    /// Serializes the transactions to a JSON-string or buffer.
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => {
                let mut transactions = serializer.serialize_seq(Some(self.transactions.len()))?;
                for transaction in self.transactions.values() {
                    transactions.serialize_element(transaction)?;
                }
                transactions.end()
            }
            false => ToBytesSerializer::serialize_with_size_encoding(self, serializer),
        }
    }
}

impl<'de, N: Network> Deserialize<'de> for Transactions<N> {
    /// Deserializes the transactions from a JSON-string or buffer.
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => {
                use core::marker::PhantomData;
                use serde::de::{SeqAccess, Visitor};

                struct TransactionsDeserializer<N: Network>(PhantomData<N>);

                impl<'de, N: Network> Visitor<'de> for TransactionsDeserializer<N> {
                    type Value = Vec<Transaction<N>>;

                    fn expecting(&self, formatter: &mut Formatter) -> fmt::Result {
                        formatter.write_str("Vec<Transaction> sequence.")
                    }

                    fn visit_seq<A: SeqAccess<'de>>(self, mut seq: A) -> Result<Self::Value, A::Error> {
                        let mut transactions = Vec::new();
                        while let Some(transaction) = seq.next_element()? {
                            transactions.push(transaction);
                        }
                        Ok(transactions)
                    }
                }

                Ok(Self::from(&deserializer.deserialize_seq(TransactionsDeserializer(PhantomData))?))
            }
            false => FromBytesDeserializer::<Self>::deserialize_with_size_encoding(deserializer, "transactions"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    const ITERATIONS: usize = 10;

    #[test]
    fn test_serde_json() {
        let rng = &mut TestRng::default();

        let check_serde_json = |expected: &Transactions<CurrentNetwork>| {
            // Serialize
            let expected_string = &expected.to_string();
            let candidate_string = serde_json::to_string(&expected).unwrap();

            // Deserialize
            assert_eq!(*expected, Transactions::from_str(expected_string).unwrap());
            assert_eq!(*expected, serde_json::from_str(&candidate_string).unwrap());
        };

        // Check the serialization.
        check_serde_json(crate::vm::test_helpers::sample_genesis_block(rng).transactions());

        for i in 0..ITERATIONS {
            let transaction = if i % 2 == 0 {
                crate::vm::test_helpers::sample_deployment_transaction(rng)
            } else {
                crate::vm::test_helpers::sample_execution_transaction(rng)
            };

            // Construct the transactions.
            let expected: Transactions<CurrentNetwork> = [transaction.clone(), transaction].into_iter().collect();
            // Check the serialization.
            check_serde_json(&expected);
        }
    }

    #[test]
    fn test_bincode() {
        let rng = &mut TestRng::default();

        let check_bincode = |expected: &Transactions<CurrentNetwork>| {
            // Serialize
            let expected_bytes = expected.to_bytes_le().unwrap();
            let expected_bytes_with_size_encoding = bincode::serialize(&expected).unwrap();
            assert_eq!(&expected_bytes[..], &expected_bytes_with_size_encoding[8..]);

            // Deserialize
            assert_eq!(*expected, Transactions::read_le(&expected_bytes[..]).unwrap());
            assert_eq!(*expected, bincode::deserialize(&expected_bytes_with_size_encoding[..]).unwrap());
        };

        // Check the serialization.
        check_bincode(crate::vm::test_helpers::sample_genesis_block(rng).transactions());

        for transaction in [
            crate::vm::test_helpers::sample_deployment_transaction(rng),
            crate::vm::test_helpers::sample_execution_transaction(rng),
        ] {
            for i in 0..ITERATIONS {
                // Construct the transactions.
                let expected: Transactions<CurrentNetwork> = vec![transaction.clone(); i].into_iter().collect();
                // Check the serialization.
                check_bincode(&expected);
            }
        }
    }
}
