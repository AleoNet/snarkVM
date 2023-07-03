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

impl<N: Network> FromBytes for Ratify<N> {
    /// Reads the ratify object from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the version.
        let version = u8::read_le(&mut reader)?;
        // Ensure the version is valid.
        if version != 0 {
            return Err(error("Invalid ratify version"));
        }

        let variant = Variant::read_le(&mut reader)?;
        let literal = match variant {
            0 => {
                // Read the address.
                let address: Address<N> = FromBytes::read_le(&mut reader)?;
                // Read the amount.
                let amount: u64 = FromBytes::read_le(&mut reader)?;
                // Return the ratify object.
                Self::ProvingReward(address, amount)
            }
            1 => {
                // Read the address.
                let address: Address<N> = FromBytes::read_le(&mut reader)?;
                // Read the amount.
                let amount: u64 = FromBytes::read_le(&mut reader)?;
                // Return the ratify object.
                Self::StakingReward(address, amount)
            }
            2.. => return Err(error(format!("Failed to decode ratify object variant {variant}"))),
        };
        Ok(literal)
    }
}

impl<N: Network> ToBytes for Ratify<N> {
    /// Writes the ratify object to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Write the version.
        0u8.write_le(&mut writer)?;

        match self {
            Self::ProvingReward(address, amount) => {
                (0 as Variant).write_le(&mut writer)?;
                address.write_le(&mut writer)?;
                amount.write_le(&mut writer)
            }
            Self::StakingReward(address, amount) => {
                (1 as Variant).write_le(&mut writer)?;
                address.write_le(&mut writer)?;
                amount.write_le(&mut writer)
            }
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

        for expected in crate::ratify::test_helpers::sample_ratify_objects(rng) {
            // Check the byte representation.
            let expected_bytes = expected.to_bytes_le().unwrap();
            assert_eq!(expected, Ratify::read_le(&expected_bytes[..]).unwrap());
            assert!(Ratify::<CurrentNetwork>::read_le(&expected_bytes[1..]).is_err());
        }
    }
}
