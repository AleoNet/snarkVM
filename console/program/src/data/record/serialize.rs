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

impl<N: Network> Serialize for Record<N, Plaintext<N>> {
    /// Serializes the record plaintext into a string or as bytes.
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            // true => serializer.collect_str(self),
            true => {
                let mut request = serializer.serialize_struct("Record<N, Plaintext<N>>", 3)?;
                request.serialize_field("owner", &self.owner.to_string())?;
                request.serialize_field("gates", &self.gates.to_string())?;
                request.serialize_field(
                    "data",
                    &self
                        .data
                        .iter()
                        .map(|(_identifier, entry)| (_identifier.to_string(), entry.to_string()))
                        .collect::<IndexMap<_, _>>(),
                )?;
                request.serialize_field("_nonce", &self.nonce)?;
                request.end()
            }
            false => ToBytesSerializer::serialize_with_size_encoding(self, serializer),
        }
    }
}

impl<'de, N: Network> Deserialize<'de> for Record<N, Plaintext<N>> {
    /// Deserializes the record plaintext from a string or bytes.
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        // TODO: Owner, Balance, and Data should implement from_value.
        match deserializer.is_human_readable() {
            // true => FromStr::from_str(&String::deserialize(deserializer)?).map_err(de::Error::custom),
            true => {
                let record = serde_json::Value::deserialize(deserializer)?;
                let owner: Owner<N, Plaintext<N>> = {
                    let address = record["owner"]
                        .as_str()
                        .ok_or_else(|| de::Error::custom("failed to deserialize the record owner from a string"))?;
                    if address.contains("private") {
                        Owner::Private(
                            Plaintext::from_str(address.split('.').next().unwrap()).map_err(de::Error::custom)?,
                        )
                    } else {
                        Owner::Public(Address::from_str(address.split('.').next().unwrap()).map_err(de::Error::custom)?)
                    }
                };
                let gates: Balance<N, Plaintext<N>> = {
                    let gates = record["gates"]
                        .as_str()
                        .ok_or_else(|| de::Error::custom("failed to deserialize the record gates from a string"))?;
                    if gates.contains("private") {
                        Balance::Private(
                            Plaintext::from_str(gates.split('.').next().unwrap()).map_err(de::Error::custom)?,
                        )
                    } else {
                        Balance::Public(U64::from_str(gates.split('.').next().unwrap()).map_err(de::Error::custom)?)
                    }
                };
                let data = {
                    let data = record["data"]
                        .as_object()
                        .ok_or_else(|| de::Error::custom("failed to deserialize the record data from a string"))?;
                    data.iter()
                        .map(|(identifier, entry)| {
                            let identifier = Identifier::from_str(identifier).map_err(de::Error::custom)?;
                            let entry = Entry::from_str(entry.as_str().ok_or_else(|| {
                                de::Error::custom("failed to deserialize the record entry from a string")
                            })?)
                            .map_err(de::Error::custom)?;
                            Ok((identifier, entry))
                        })
                        .collect::<Result<IndexMap<_, _>, _>>()?
                };
                let nonce = serde_json::from_value(record["_nonce"].clone()).map_err(de::Error::custom)?;

                Ok(Record::<N, Plaintext<N>>::from_plaintext(owner, gates, data, nonce).map_err(de::Error::custom)?)
            }
            false => FromBytesDeserializer::<Self>::deserialize_with_size_encoding(deserializer, "record plaintext"),
        }
    }
}

impl<N: Network> Serialize for Record<N, Ciphertext<N>> {
    /// Serializes the record ciphertext into a string or as bytes.
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => serializer.collect_str(self),
            false => ToBytesSerializer::serialize_with_size_encoding(self, serializer),
        }
    }
}

impl<'de, N: Network> Deserialize<'de> for Record<N, Ciphertext<N>> {
    /// Deserializes the record ciphertext from a string or bytes.
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => FromStr::from_str(&String::deserialize(deserializer)?).map_err(de::Error::custom),
            false => FromBytesDeserializer::<Self>::deserialize_with_size_encoding(deserializer, "record ciphertext"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network::Testnet3;

    type CurrentNetwork = Testnet3;

    const ITERATIONS: u64 = 1;

    #[test]
    fn test_serde_json() -> Result<()> {
        for _ in 0..ITERATIONS {
            // Sample a new record.
            let expected = Record::<CurrentNetwork, Plaintext<CurrentNetwork>>::from_str(
                "{ owner: aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah.private, gates: 5u64.private, token_amount: 100u64.private, _nonce: 0group.public }",
            )?;
            println!("{}", serde_json::to_string_pretty(&expected)?);

            // Serialize
            let expected_string = &expected.to_string();
            let candidate_string = serde_json::to_string(&expected)?;
            assert_eq!(expected_string, serde_json::Value::from_str(&candidate_string)?.as_str().unwrap());

            // Deserialize
            assert_eq!(expected, Record::from_str(expected_string)?);
            assert_eq!(expected, serde_json::from_str(&candidate_string)?);
        }
        Ok(())
    }

    #[test]
    fn test_bincode() -> Result<()> {
        for _ in 0..ITERATIONS {
            // Sample a new record.
            let expected = Record::<CurrentNetwork, Plaintext<CurrentNetwork>>::from_str(
                "{ owner: aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah.private, gates: 5u64.private, token_amount: 100u64.private, _nonce: 0group.public }",
            )?;

            // Serialize
            let expected_bytes = expected.to_bytes_le()?;
            let expected_bytes_with_size_encoding = bincode::serialize(&expected)?;
            assert_eq!(&expected_bytes[..], &expected_bytes_with_size_encoding[8..]);

            // Deserialize
            assert_eq!(expected, Record::read_le(&expected_bytes[..])?);
            assert_eq!(expected, bincode::deserialize(&expected_bytes_with_size_encoding[..])?);
        }
        Ok(())
    }
}
