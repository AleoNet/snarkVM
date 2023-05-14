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
