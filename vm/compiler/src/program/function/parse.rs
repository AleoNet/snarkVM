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

impl<N: Network> Parser for Function<N> {
    /// Parses a string into a function.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the 'function' keyword from the string.
        let (string, _) = tag(Self::type_name())(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the function name from the string.
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
            // Initialize a new function.
            let mut function = Self::new(name);
            if let Err(error) = inputs.iter().cloned().try_for_each(|input| function.add_input(input)) {
                eprintln!("{error}");
                return Err(error);
            }
            if let Err(error) =
                instructions.iter().cloned().try_for_each(|instruction| function.add_instruction(instruction))
            {
                eprintln!("{error}");
                return Err(error);
            }
            if let Err(error) = outputs.iter().cloned().try_for_each(|output| function.add_output(output)) {
                eprintln!("{error}");
                return Err(error);
            }
            Ok::<_, Error>(function)
        })(string)
    }
}

impl<N: Network> FromStr for Function<N> {
    type Err = Error;

    /// Returns a function from a string literal.
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

impl<N: Network> Debug for Function<N> {
    /// Prints the function as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for Function<N> {
    /// Prints the function as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        // Write the function to a string.
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
    fn test_function_parse() {
        let function = Function::<CurrentNetwork>::parse(
            r"
function foo:
    input r0 as field.public;
    input r1 as field.private;
    add r0 r1 into r2;
    output r2 as field.private;",
        )
        .unwrap()
        .1;
        assert_eq!("foo", function.name().to_string());
        assert_eq!(2, function.inputs.len());
        assert_eq!(1, function.instructions.len());
        assert_eq!(1, function.outputs.len());
    }

    #[test]
    fn test_function_parse_cast() {
        let function = Function::<CurrentNetwork>::parse(
            r"
function foo:
    input r0 as token.record;
    cast r0.owner r0.balance r0.token_amount into r1 as token.record;
    output r1 as token.record;",
        )
        .unwrap()
        .1;
        assert_eq!("foo", function.name().to_string());
        assert_eq!(1, function.inputs.len());
        assert_eq!(1, function.instructions.len());
        assert_eq!(1, function.outputs.len());
    }

    #[test]
    fn test_function_display() {
        let expected = r"function foo:
    input r0 as field.public;
    input r1 as field.private;
    add r0 r1 into r2;
    output r2 as field.private;";
        let function = Function::<CurrentNetwork>::parse(expected).unwrap().1;
        assert_eq!(expected, format!("{function}"),);
    }
}
