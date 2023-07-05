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

impl<N: Network> Parser for ArrayType<N> {
    /// Parses a string into an array type.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the opening brackets and count the number of brackets.
        let (string, num_dimensions) = map_res(
            many1_count(pair(tag("["), Sanitizer::parse_whitespaces)),
            |num_dimensions| match num_dimensions {
                num_dimensions if (0 < num_dimensions) && (num_dimensions <= N::MAX_DATA_DEPTH) => Ok(num_dimensions),
                _ => Err(error("Number of dimensions exceeds the maximum")),
            },
        )(string)?;

        // Parse the whitespaces from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;

        // Parse the innermost element type, note that this must either be `LiteralType` or `Identifier`.
        let (string, element_type) = alt((
            map(LiteralType::parse, |literal_type| PlaintextType::Literal(literal_type)),
            map(Identifier::parse, |identifier| PlaintextType::Struct(identifier)),
        ))(string)?;

        // A helper function to parse the semicolon, length, and closing bracket.
        fn parse_length(string: &str) -> ParserResult<u32> {
            // Parse the whitespaces from the string.
            let (string, _) = Sanitizer::parse_whitespaces(string)?;
            // Parse the semicolon.
            let (string, _) = tag(";")(string)?;
            // Parse the whitespaces from the string.
            let (string, _) = Sanitizer::parse_whitespaces(string)?;
            // Parse the length from the string.
            let (string, length) =
                map_res(recognize(many1(one_of("0123456789"))), |digits: &str| digits.parse::<u32>())(string)?;
            // Parse the whitespaces from the string.
            let (string, _) = Sanitizer::parse_whitespaces(string)?;
            // Parse the closing bracket.
            let (string, _) = tag("]")(string)?;
            Ok((string, length))
        }

        // Parse the lengths, `num_dimensions` times.
        let (string, lengths) = count(parse_length, num_dimensions)(string)?;

        // Construct the element type from the lengths.
        map_res(take(0usize), move |_| -> Result<_, Error> {
            // Construct an iterator over the lengths.
            let mut lengths = lengths.iter().rev();
            // Get the last length and construct the array type.
            // Note that this unwrap is safe since we have already checked that `num_dimensions` is greater than zero.
            let mut array_type = ArrayType::new(element_type.clone(), U32::new(*lengths.next().unwrap()))?;
            // Construct the array type from the remaining lengths.
            for length in lengths {
                array_type = ArrayType::new(PlaintextType::Array(array_type), U32::new(*length))?;
            }
            Ok(array_type)
        })(string)
    }
}

impl<N: Network> FromStr for ArrayType<N> {
    type Err = Error;

    /// Returns an array type from a string literal.
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

impl<N: Network> Debug for ArrayType<N> {
    /// Prints the array type as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for ArrayType<N> {
    /// Prints the array type as a string.
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        // Get the lengths and the innermost element type.
        let mut lengths = Vec::with_capacity(N::MAX_DATA_DEPTH);
        lengths.push(self.length());
        let mut element_type = self.element_type();
        for _ in 1..N::MAX_DATA_DEPTH {
            match element_type {
                PlaintextType::Array(array_type) => {
                    lengths.push(array_type.length());
                    element_type = array_type.element_type();
                }
                _ => break,
            }
        }
        // If the innermost element type is an array, then return an error.
        if let PlaintextType::Array(_) = element_type {
            panic!("Array type exceeds the maximum depth")
        }
        // Print the opening brackets.
        for _ in 0..lengths.len() {
            write!(f, "[")?;
        }
        // Print the innermost element type.
        Display::fmt(&element_type, f)?;
        // Print the lengths.
        for length in lengths.iter().rev() {
            write!(f, "; {}]", length)?;
        }
        Ok(())
    }
}
