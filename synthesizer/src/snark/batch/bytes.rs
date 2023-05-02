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

const PROVING: u8 = 0;
const VERIFYING: u8 = 1;

impl<N: Network> FromBytes for KeyBatch<N> {
    /// Reads the proving key batch from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the version.
        let version = u16::read_le(&mut reader)?;
        // Ensure the version is valid.
        if version != 0 {
            return Err(error("Invalid verifying key version"));
        }
        // Read the mode.
        let mode = u8::read_le(&mut reader)?;
        let mode = match mode {
            PROVING => KeyMode::Proving,
            VERIFYING => KeyMode::Verifying,
            _ => return Err(error("Invalid key mode")),
        };
        // Read the number of keys.
        let batch_len = usize::try_from(u32::read_le(&mut reader)?);
        let batch_len = if let Ok(batch_len) = batch_len {
            batch_len
        } else {
            return Err(error("Could not convert u32 to usize"));
        };
        let mut batch = Vec::with_capacity(batch_len);
        // Read the keys
        for _ in 0..batch_len {
            match mode {
                KeyMode::Proving => {
                    batch.push(Key::ProvingKey(ProvingKey::new(Arc::new(FromBytes::read_le(&mut reader)?))));
                }
                KeyMode::Verifying => {
                    batch.push(Key::VerifyingKey(VerifyingKey::new(Arc::new(FromBytes::read_le(&mut reader)?))));
                }
            }
        }
        Ok(Self { batch, mode })
    }
}

impl<N: Network> ToBytes for KeyBatch<N> {
    /// Writes the proving key to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Write the version.
        0u16.write_le(&mut writer)?;
        // Write the key types
        match self.mode {
            KeyMode::Proving => PROVING.write_le(&mut writer)?,
            KeyMode::Verifying => VERIFYING.write_le(&mut writer)?,
        }
        // Write the number of Keys.
        let batch_len = u32::try_from(self.batch.len());
        if batch_len.is_err() {
            return Err(error("Could not convert usize to u32"));
        } else {
            batch_len.unwrap().write_le(&mut writer)?;
        };
        // Write the bytes.
        for key in &self.batch {
            match key {
                Key::VerifyingKey(vk) => vk.write_le(&mut writer)?,
                Key::ProvingKey(pk) => pk.write_le(&mut writer)?,
            }
        }
        Ok(())
    }
}
