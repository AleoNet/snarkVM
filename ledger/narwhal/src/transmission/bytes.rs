// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use super::*;

impl<N: Network> FromBytes for Transmission<N> {
    /// Reads the transmission from the buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the version.
        let version = u8::read_le(&mut reader)?;
        // Ensure the version is valid.
        if version != 0 {
            return Err(error("Invalid transmission version"));
        }

        // Read the variant.
        let variant = u8::read_le(&mut reader)?;
        // Match the variant.
        match variant {
            0 => Ok(Self::Ratification),
            1 => Ok(Self::Solution(transmission_from_bytes_le(&mut reader)?)),
            2 => Ok(Self::Transaction(transmission_from_bytes_le(&mut reader)?)),
            3.. => Err(error("Invalid transmission variant")),
        }
    }
}

impl<N: Network> ToBytes for Transmission<N> {
    /// Writes the transmission to the buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Write the version.
        0u8.write_le(&mut writer)?;
        // Write the transmission.
        match self {
            Self::Ratification => 0u8.write_le(&mut writer),
            Self::Solution(solution) => {
                1u8.write_le(&mut writer)?;
                transmission_to_bytes_le(solution, &mut writer)
            }
            Self::Transaction(transaction) => {
                2u8.write_le(&mut writer)?;
                transmission_to_bytes_le(transaction, &mut writer)
            }
        }
    }
}

/// Reads the transmission from the buffer.
fn transmission_from_bytes_le<T: FromBytes + ToBytes + Send + 'static, R: Read>(mut reader: R) -> IoResult<Data<T>> {
    // Read the number of bytes.
    let num_bytes = u32::read_le(&mut reader)?;
    // Read the bytes.
    let bytes = (0..num_bytes).map(|_| u8::read_le(&mut reader)).collect::<IoResult<Vec<u8>>>()?;
    // Return the data.
    Ok(Data::Buffer(Bytes::from(bytes)))
}

/// Writes the transmission to the buffer.
fn transmission_to_bytes_le<T: FromBytes + ToBytes + Send + 'static, W: Write>(
    transmission: &Data<T>,
    mut writer: W,
) -> IoResult<()> {
    // Write the transmission.
    match transmission {
        Data::Object(x) => {
            let bytes = x.to_bytes_le().map_err(|e| error(e.to_string()))?;
            // Write the number of bytes.
            u32::try_from(bytes.len()).map_err(|e| error(e.to_string()))?.write_le(&mut writer)?;
            // Write the bytes.
            writer.write_all(&bytes)
        }
        Data::Buffer(bytes) => {
            // Write the number of bytes.
            u32::try_from(bytes.len()).map_err(|e| error(e.to_string()))?.write_le(&mut writer)?;
            // Write the bytes.
            writer.write_all(bytes)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_bytes() {
        let rng = &mut TestRng::default();

        for expected in crate::transmission::test_helpers::sample_transmissions(rng) {
            // Check the byte representation.
            let expected_bytes = expected.to_bytes_le().unwrap();
            assert_eq!(expected, Transmission::read_le(&expected_bytes[..]).unwrap());
            assert!(Transmission::<CurrentNetwork>::read_le(&expected_bytes[1..]).is_err());
        }
    }
}
