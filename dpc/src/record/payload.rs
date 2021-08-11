// Copyright (C) 2019-2021 Aleo Systems Inc.
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

use snarkvm_utilities::{FromBytes, ToBytes};

use std::io::{Read, Result as IoResult, Write};

pub const PAYLOAD_SIZE: usize = 128;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Payload([u8; PAYLOAD_SIZE]);

impl Payload {
    pub fn from(bytes: &[u8]) -> Self {
        assert!(bytes.len() <= PAYLOAD_SIZE);

        // Pad the bytes up to PAYLOAD_SIZE.
        let mut buffer = bytes.to_vec();
        buffer.resize(PAYLOAD_SIZE, 0u8);

        // Copy exactly PAYLOAD_SIZE.
        let mut payload = [0u8; PAYLOAD_SIZE];
        payload.copy_from_slice(&buffer);

        Self(payload)
    }

    pub fn is_empty(&self) -> bool {
        self.0 == [0u8; PAYLOAD_SIZE]
    }

    pub fn as_any(&self) -> &dyn std::any::Any {
        self
    }

    pub const fn size(&self) -> usize {
        PAYLOAD_SIZE
    }
}

impl ToBytes for Payload {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.0.write_le(&mut writer)
    }
}

impl FromBytes for Payload {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(Self(FromBytes::read_le(&mut reader)?))
    }
}

impl Default for Payload {
    fn default() -> Self {
        Self([0u8; PAYLOAD_SIZE])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_utilities::UniformRand;

    #[test]
    fn test_payload_from() {
        let rng = &mut rand::thread_rng();

        // Create a random byte array, construct a payload from it, and check its byte array matches.
        for i in 0..PAYLOAD_SIZE {
            let expected_payload = (0..i).map(|_| u8::rand(rng)).collect::<Vec<u8>>();
            let candidate_payload = Payload::from(&expected_payload).to_bytes_le().unwrap();
            assert_eq!(expected_payload, candidate_payload[0..i]);
            assert_eq!(vec![0u8; PAYLOAD_SIZE - i], candidate_payload[i..]);
        }
    }
}
