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

impl<N: Network> FromBytes for Origin<N> {
    /// Reads the origin from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let variant = Variant::read_le(&mut reader)?;
        let origin = match variant {
            0 => {
                let commitment: Field<N> = FromBytes::read_le(&mut reader)?;

                Self::Commitment(commitment)
            }
            1 => {
                let state_root: N::StateRoot = FromBytes::read_le(&mut reader)?;

                Self::StateRoot(state_root)
            }
            2.. => return Err(error(format!("Failed to decode transition origin variant {variant}"))),
        };
        Ok(origin)
    }
}

impl<N: Network> ToBytes for Origin<N> {
    /// Writes the origin to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        match self {
            Self::Commitment(commitment) => {
                (0 as Variant).write_le(&mut writer)?;
                commitment.write_le(&mut writer)
            }
            Self::StateRoot(state_root) => {
                (1 as Variant).write_le(&mut writer)?;
                state_root.write_le(&mut writer)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    const ITERATIONS: u32 = 1000;

    fn check_bytes(expected: Origin<CurrentNetwork>) -> Result<()> {
        // Check the byte representation.
        let expected_bytes = expected.to_bytes_le()?;
        assert_eq!(expected, Origin::read_le(&expected_bytes[..])?);
        Ok(())
    }

    #[test]
    fn test_bytes() -> Result<()> {
        let rng = &mut TestRng::default();

        for _ in 0..ITERATIONS {
            // Commitment
            check_bytes(Origin::<CurrentNetwork>::Commitment(Uniform::rand(rng)))?;

            // StateRoot
            check_bytes(Origin::<CurrentNetwork>::StateRoot(Uniform::rand(rng)))?;
        }
        Ok(())
    }
}
