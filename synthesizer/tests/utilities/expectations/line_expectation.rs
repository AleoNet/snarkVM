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

/// An expectation that treats contents of a file as a sequence of expected results.
/// LineExpectation assumes that the file is a YAML sequence of strings.
pub struct LineExpectation {
    pub path: PathBuf,
    pub content: serde_yaml::Sequence,
    pub rewrite: bool,
}

impl Expectation for LineExpectation {
    type Output = Vec<String>;
    type Test = Vec<String>;

    /// Loads the expectation from the given path.
    /// If the `REWRITE_EXPECTATIONS` environment variable is set, the expectation is loaded as empty.
    fn load<P: AsRef<Path>>(input: P) -> Result<Self> {
        let rewrite = std::env::var("REWRITE_EXPECTATIONS").is_ok();
        let content = match rewrite {
            true => Vec::new(),
            false => serde_yaml::from_str(&std::fs::read_to_string(input.as_ref())?)?,
        };

        Ok(Self { path: input.as_ref().to_path_buf(), content, rewrite })
    }

    /// Checks the expectation against the given output.
    fn check(&self, test: &Self::Test, output: &Self::Output) -> Result<()> {
        if !self.rewrite {
            self.content.iter().zip_eq(test.iter().zip_eq(output.iter())).try_for_each(
                |(expected, (test, actual))| match expected.as_str() {
                    Some(expected) if expected != actual => bail!("{}", print_difference(test, expected, actual)),
                    None => bail!("Expected string"),
                    _ => Ok(()),
                },
            )?;
        }
        Ok(())
    }

    /// Saves the expectation to the given path.
    fn save(&self, output: &Self::Output) -> Result<()> {
        if self.rewrite {
            let content = serde_yaml::to_string(&output)?;
            std::fs::write(&self.path, content)?;
        }
        Ok(())
    }
}
