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

impl<E: Environment, I: IntegerType> Serialize for Integer<E, I> {
    /// Serializes the integer into a string or as bytes.
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => serializer.collect_str(self),
            false => ToBytesSerializer::serialize(self, serializer),
        }
    }
}

impl<'de, E: Environment, I: IntegerType> Deserialize<'de> for Integer<E, I> {
    /// Deserializes the integer from a string or bytes.
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => FromStr::from_str(&String::deserialize(deserializer)?).map_err(de::Error::custom),
            false => FromBytesDeserializer::<Self>::deserialize(deserializer, "integer", Self::size_in_bytes()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network_environment::Console;

    type CurrentEnvironment = Console;

    const ITERATIONS: u64 = 1000;

    fn check_serde_json<I: IntegerType>() -> Result<()> {
        for _ in 0..ITERATIONS {
            // Sample a new integer.
            let expected = Integer::<CurrentEnvironment, I>::new(Uniform::rand(&mut test_rng()));

            // Serialize
            let expected_string = &expected.to_string();
            let candidate_string = serde_json::to_string(&expected)?;
            assert_eq!(expected_string, serde_json::Value::from_str(&candidate_string)?.as_str().unwrap());

            // Deserialize
            assert_eq!(expected, Integer::from_str(expected_string)?);
            assert_eq!(expected, serde_json::from_str(&candidate_string)?);
        }
        Ok(())
    }

    fn check_bincode<I: IntegerType>() -> Result<()> {
        for _ in 0..ITERATIONS {
            // Sample a new integer.
            let expected = Integer::<CurrentEnvironment, I>::new(Uniform::rand(&mut test_rng()));

            // Serialize
            let expected_bytes = expected.to_bytes_le()?;
            assert_eq!(&expected_bytes[..], &bincode::serialize(&expected)?[..]);

            // Deserialize
            assert_eq!(expected, Integer::read_le(&expected_bytes[..])?);
            assert_eq!(expected, bincode::deserialize(&expected_bytes[..])?);
        }
        Ok(())
    }

    #[test]
    fn test_serde_json() -> Result<()> {
        check_serde_json::<u8>()?;
        check_serde_json::<u16>()?;
        check_serde_json::<u32>()?;
        check_serde_json::<u64>()?;
        check_serde_json::<u128>()?;

        check_serde_json::<i8>()?;
        check_serde_json::<i16>()?;
        check_serde_json::<i32>()?;
        check_serde_json::<i64>()?;
        check_serde_json::<i128>()?;
        Ok(())
    }

    #[test]
    fn test_bincode() -> Result<()> {
        check_bincode::<u8>()?;
        check_bincode::<u16>()?;
        check_bincode::<u32>()?;
        check_bincode::<u64>()?;
        check_bincode::<u128>()?;

        check_bincode::<i8>()?;
        check_bincode::<i16>()?;
        check_bincode::<i32>()?;
        check_bincode::<i64>()?;
        check_bincode::<i128>()?;
        Ok(())
    }
}
