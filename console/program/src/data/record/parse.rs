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

impl<N: Network> Parser for Record<N, Plaintext<N>> {
    /// Parses a string as a record: `{ owner: address, balance: u64, identifier_0: plaintext_0, ..., identifier_n: plaintext_n }`.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        /// Parses a sanitized pair: `identifier: plaintext`.
        fn parse_pair<N: Network>(string: &str) -> ParserResult<(Identifier<N>, Plaintext<N>)> {
            // Parse the whitespace and comments from the string.
            let (string, _) = Sanitizer::parse(string)?;
            // Parse the identifier from the string.
            let (string, identifier) = Identifier::parse(string)?;
            // Parse the ":" from the string.
            let (string, _) = tag(":")(string)?;
            // Parse the plaintext from the string.
            let (string, plaintext) = Plaintext::parse(string)?;
            // Return the identifier and plaintext.
            Ok((string, (identifier, plaintext)))
        }

        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the "{" from the string.
        let (string, _) = tag("{")(string)?;

        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the "owner" tag from the string.
        let (string, _) = tag("owner")(string)?;
        // Parse the ":" from the string.
        let (string, _) = tag(":")(string)?;
        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the owner from the string.
        let (string, owner) = Address::parse(string)?;
        // Parse the "," from the string.
        let (string, _) = tag(",")(string)?;

        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the "balance" tag from the string.
        let (string, _) = tag("balance")(string)?;
        // Parse the ":" from the string.
        let (string, _) = tag(":")(string)?;
        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the balance from the string.
        let (string, balance) = U64::parse(string)?;
        // Parse the "," from the string.
        let (string, _) = tag(",")(string)?;

        // {
        //     // Parse the whitespace and comments from the string.
        //     let (string, _) = Sanitizer::parse(string)?;
        //     // Parse the "owner" tag from the string.
        //     let (string, _) = tag("owner")(string)?;
        //     // Parse the " as " from the string.
        //     let (string, _) = tag(" as ")(string)?;
        //     // Parse the whitespace and comments from the string.
        //     let (string, _) = Sanitizer::parse(string)?;
        //     // Parse the owner from the string.
        //     let (string, (owner, is_public)) = alt((
        //         map(pair(Address::parse, tag(".public")), |(owner, _)| (owner, false)), // IsPrivate = false
        //         map(pair(Address::parse, tag(".private")), |(owner, _)| (owner, true)), // IsPrivate = true
        //     ))(string)?;
        //     // Parse the ";" from the string.
        //     let (string, _) = tag(";")(string)?;
        //
        //     // Parse the whitespace and comments from the string.
        //     let (string, _) = Sanitizer::parse(string)?;
        //     // Parse the "balance" tag from the string.
        //     let (string, _) = tag("balance")(string)?;
        //     // Parse the " as " from the string.
        //     let (string, _) = tag(" as ")(string)?;
        //     // Parse the whitespace and comments from the string.
        //     let (string, _) = Sanitizer::parse(string)?;
        //     // Parse the balance from the string.
        //     let (string, (balance, is_public)) = alt((
        //         map(pair(U64::parse, tag(".public")), |(balance, _)| (balance, false)), // IsPrivate = false
        //         map(pair(U64::parse, tag(".private")), |(balance, _)| (balance, true)), // IsPrivate = true
        //     ))(string)?;
        //     // Parse the ";" from the string.
        //     let (string, _) = tag(";")(string)?;
        // }

        // Parse the members.
        let (string, members) = map_res(separated_list1(tag(","), parse_pair), |members: Vec<_>| {
            // Ensure the members has no duplicate names.
            if has_duplicates(members.iter().map(|(name, ..)| name)) {
                return Err(error(format!("Duplicate member in record")));
            }
            // Ensure the number of interfaces is within `N::MAX_DATA_ENTRIES`.
            match members.len() <= N::MAX_DATA_ENTRIES {
                true => Ok(members),
                false => Err(error(format!("Found a record that exceeds size ({})", members.len()))),
            }
        })(string)?;
        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the '}' from the string.
        let (string, _) = tag("}")(string)?;
        // Output the record.
        Ok((
            string,
            Record { owner, balance, data: IndexMap::from_iter(members.into_iter()) },
        ))
    }
}

impl<N: Network> FromStr for Record<N, Plaintext<N>> {
    type Err = Error;

    /// Returns a record from a string literal.
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

impl<N: Network> Debug for Record<N, Plaintext<N>> {
    /// Prints the record as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

#[allow(clippy::format_push_string)]
impl<N: Network> Display for Record<N, Plaintext<N>> {
    /// Prints the record as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        // Prints the record, i.e. { owner: aleo1xxx, balance: 10u64, first: 10i64 }
        let owner = self.owner().map_err(|_| fmt::Error)?;
        let balance = self.balance().map_err(|_| fmt::Error)?;

        let mut output = format!("{{ owner: {owner}, balance: {balance}, ");
        for (identifier, plaintext) in self.data.iter() {
            output += &format!("{identifier}: {plaintext}, ");
        }
        output.pop(); // trailing space
        output.pop(); // trailing comma
        output += " }";
        write!(f, "{output}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_parse() -> Result<()> {
        // Sanity check.
        let expected = "{ owner: aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah, balance: 99u64 }";
        let (remainder, candidate) = Record::<CurrentNetwork>::parse(expected)?;
        assert_eq!(expected, candidate.to_string());
        assert_eq!("", remainder);

        let expected =
            "{ owner: aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah, balance: 99u64, foo: 5u8 }";
        let (remainder, candidate) = Record::<CurrentNetwork>::parse(expected)?;
        assert_eq!(expected, candidate.to_string());
        assert_eq!("", remainder);

        Ok(())
    }

    #[test]
    fn test_parse_fails() -> Result<()> {
        // Missing owner.
        let expected = "{ balance: 99u64, foo: 5u8 }";
        assert!(Plaintext::<CurrentNetwork>::parse(expected).is_err());

        Ok(())
    }
}
