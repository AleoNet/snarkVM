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

impl<N: Network> FromStr for PuzzleSolutions<N> {
    type Err = Error;

    /// Initializes the solutions from a JSON-string.
    fn from_str(solutions: &str) -> Result<Self, Self::Err> {
        Ok(serde_json::from_str(solutions)?)
    }
}

impl<N: Network> Debug for PuzzleSolutions<N> {
    /// Prints the solutions as a JSON-string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for PuzzleSolutions<N> {
    /// Displays the solutions as a JSON-string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", serde_json::to_string(self).map_err::<fmt::Error, _>(ser::Error::custom)?)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_string() -> Result<()> {
        let mut rng = TestRng::default();

        // Sample random solutions.
        let expected = crate::solutions::serialize::tests::sample_solutions(&mut rng);

        // Check the string representation.
        let candidate = format!("{expected}");
        assert_eq!(expected, PuzzleSolutions::from_str(&candidate)?);

        Ok(())
    }
}
