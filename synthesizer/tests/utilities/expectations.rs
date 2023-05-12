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

/// An expectation that treats the contents of a file as the expected result.
pub struct FileExpectation {
    pub path: PathBuf,
    pub content: String,
    pub rewrite: bool,
}

impl Expectation for FileExpectation {
    type Output = String;
    type Test = String;

    /// Loads the expectation from the given path.
    /// If the `REWRITE_EXPECTATIONS` environment variable is set, the expectation is loaded as empty.
    fn load<P: AsRef<Path>>(input: P) -> Result<Self> {
        let rewrite = std::env::var("REWRITE_EXPECTATIONS").is_ok();
        let content = match rewrite {
            true => String::new(),
            false => std::fs::read_to_string(input.as_ref())?,
        };

        Ok(Self { path: input.as_ref().to_path_buf(), content, rewrite })
    }

    /// Checks the expectation against the given output.
    fn check(&self, test: &Self::Test, output: &Self::Output) -> Result<()> {
        match self.rewrite {
            false if self.content != *output => bail!("{}", print_difference(&self.content, test, output)),
            _ => Ok(()),
        }
    }

    /// Saves the expectation to the given path.
    fn save(&self, output: &Self::Output) -> Result<()> {
        if self.rewrite {
            std::fs::write(&self.path, output)?;
        }
        Ok(())
    }
}

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
                |(expected, (test, actual))| {
                    let expected = expected.as_str().ok_or_else(|| anyhow!("Expected string"))?;
                    if expected != actual {
                        bail!("{}", print_difference(test, expected, actual));
                    }
                    Ok(())
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

/// Constructs the path to the expectation file corresponding to the given test file.
pub fn get_expectation_path<P: AsRef<Path>>(test_path: P) -> PathBuf {
    // Get the current directory.
    let current_dir = current_dir().expect("Failed to get current directory.");
    // Construct the path to the expectations directory.
    let expectations_dir = current_dir.join("tests/expectations");
    // Construct the path to the test directory.
    let tests_dir = current_dir.join("tests/tests");
    // Construct the path to the expectation file.
    expectations_dir.join(test_path.as_ref().to_path_buf().strip_prefix(tests_dir).unwrap().with_extension("out"))
}

/// Helper function to print the difference between the expected and actual output.
fn print_difference(test: &str, expected: &str, actual: &str) -> String {
    let mut message = r"
============================================================
TEST
------------------------------------------------------------
"
    .to_string();
    message.push_str(test);
    message.push_str(
        r"

============================================================
EXPECTED
------------------------------------------------------------
",
    );
    message.push_str(expected);
    message.push_str(
        r"

============================================================
ACTUAL
------------------------------------------------------------
",
    );
    message.push_str(actual);
    message.push_str(
        r"
============================================================

",
    );
    message
}
