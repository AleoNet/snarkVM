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

impl<N: Network> Parser for Closure<N> {
    /// Parses a string into a closure.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the 'closure' keyword from the string.
        let (string, _) = tag(Self::type_name())(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the closure name from the string.
        let (string, name) = Identifier::<N>::parse(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the colon ':' keyword from the string.
        let (string, _) = tag(":")(string)?;

        // Parse the inputs from the string.
        let (string, inputs) = many1(Input::parse)(string)?;
        // Parse the instructions from the string.
        let (string, instructions) = many1(Instruction::parse)(string)?;
        // Parse the outputs from the string.
        let (string, outputs) = many0(Output::parse)(string)?;

        map_res(take(0usize), move |_| {
            // Initialize a new closure.
            let mut closure = Self::new(name);
            inputs.iter().cloned().try_for_each(|input| closure.add_input(input))?;
            instructions.iter().cloned().try_for_each(|instruction| closure.add_instruction(instruction))?;
            outputs.iter().cloned().try_for_each(|output| closure.add_output(output))?;
            Ok::<_, Error>(closure)
        })(string)
    }
}

impl<N: Network> FromStr for Closure<N> {
    type Err = Error;

    /// Returns a closure from a string literal.
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

impl<N: Network> Debug for Closure<N> {
    /// Prints the closure as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for Closure<N> {
    /// Prints the closure as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        // Write the closure to a string.
        write!(f, "{} {}:", Self::type_name(), self.name)?;
        self.inputs.iter().try_for_each(|input| write!(f, "\n    {}", input))?;
        self.instructions.iter().try_for_each(|instruction| write!(f, "\n    {}", instruction))?;
        self.outputs.iter().try_for_each(|output| write!(f, "\n    {}", output))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_closure_parse() {
        let closure = Closure::<CurrentNetwork>::parse(
            r"
closure foo:
    input r0 as field;
    input r1 as field;
    add r0 r1 into r2;
    output r2 as field;",
        )
        .unwrap()
        .1;
        assert_eq!("foo", closure.name().to_string());
        assert_eq!(2, closure.inputs.len());
        assert_eq!(1, closure.instructions.len());
        assert_eq!(1, closure.outputs.len());
    }

    #[test]
    fn test_closure_parse_cast() {
        let closure = Closure::<CurrentNetwork>::parse(
            r"
closure foo:
    input r0 as token.record;
    cast r0.owner r0.gates r0.token_amount into r1 as token.record;
    output r1 as token.record;",
        )
        .unwrap()
        .1;
        assert_eq!("foo", closure.name().to_string());
        assert_eq!(1, closure.inputs.len());
        assert_eq!(1, closure.instructions.len());
        assert_eq!(1, closure.outputs.len());
    }

    #[test]
    fn test_closure_display() {
        let expected = r"closure foo:
    input r0 as field;
    input r1 as field;
    add r0 r1 into r2;
    output r2 as field;";
        let closure = Closure::<CurrentNetwork>::parse(expected).unwrap().1;
        assert_eq!(expected, format!("{closure}"),);
    }
}
