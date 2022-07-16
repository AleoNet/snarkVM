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

impl<N: Network> Parser for Value<N> {
    /// Parses a string into a value.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        alt((map(Plaintext::parse, Value::Plaintext), map(Record::parse, Value::Record)))(string)
    }
}

impl<N: Network> FromStr for Value<N> {
    type Err = Error;

    /// Parses a string into a value.
    #[inline]
    fn from_str(string: &str) -> Result<Self> {
        match Self::parse(string) {
            Ok((remainder, object)) => {
                // Ensure the remainder is empty.
                ensure!(remainder.is_empty(), "Failed to parse string. Found invalid character in: \"{remainder}\"");
                // Return the object.
                Ok(object)
            }
            Err(error) => bail!("Failed to parse string. {error}"),
        }
    }
}

impl<N: Network> Debug for Value<N> {
    /// Prints the value as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for Value<N> {
    /// Prints the value as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Value::Plaintext(plaintext) => Display::fmt(plaintext, f),
            Value::Record(record) => Display::fmt(record, f),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_value_plaintext_parse() {
        // Prepare the plaintext string.
        let string = r"{
  owner: aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah,
  gates: 5u64,
  token_amount: 100u64
}";
        // Construct a new plaintext value.
        let expected = Value::<CurrentNetwork>::from_str(string).unwrap();
        assert!(matches!(expected, Value::Plaintext(..)));
        assert_eq!(string, format!("{expected}"));
    }

    #[test]
    fn test_value_record_parse() {
        // Prepare the record string.
        let string = r"{
  owner: aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah.private,
  gates: 5u64.private,
  token_amount: 100u64.private
}";
        // Construct a new record value.
        let expected = Value::<CurrentNetwork>::from_str(string).unwrap();
        assert!(matches!(expected, Value::Record(..)));
        assert_eq!(string, format!("{expected}"));
    }
}
