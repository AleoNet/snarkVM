// Copyright 2024 Aleo Network Foundation
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

impl<N: Network> Parser for Value<N> {
    /// Parses a string into a value.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Note that the order of the parsers matters.
        alt((
            map(Future::parse, Value::Future),
            map(Plaintext::parse, Value::Plaintext),
            map(Record::parse, Value::Record),
        ))(string)
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
            Value::Future(future) => Display::fmt(future, f),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network::MainnetV0;

    type CurrentNetwork = MainnetV0;

    #[test]
    fn test_value_plaintext_parse() {
        // Prepare the plaintext string.
        let string = r"{
  owner: aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah,
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
  token_amount: 100u64.private,
  _nonce: 6122363155094913586073041054293642159180066699840940609722305038224296461351group.public
}";
        // Construct a new record value.
        let expected = Value::<CurrentNetwork>::from_str(string).unwrap();
        assert!(matches!(expected, Value::Record(..)));
        assert_eq!(string, format!("{expected}"));
    }

    #[test]
    fn test_value_future_parse() {
        // Prepare the future string.
        let string = r"{
  program_id: credits.aleo,
  function_name: transfer_public_to_private,
  arguments: [
    aleo1g8qul5a44vk22u9uuvaewdcjw4v6xg8wx0llru39nnjn7eu08yrscxe4e2,
    100000000u64
  ]
}";
        // Construct a new future value.
        let expected = Value::<CurrentNetwork>::from_str(string).unwrap();
        assert!(matches!(expected, Value::Future(..)));
        assert_eq!(string, format!("{expected}"));
    }
}
