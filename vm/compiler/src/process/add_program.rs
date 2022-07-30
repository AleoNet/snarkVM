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

impl<N: Network> Process<N> {
    /// Adds a new program to the process.
    #[inline]
    pub fn add_program(&mut self, program: &Program<N>) -> Result<()> {
        // Compute the program stack.
        let stack = Stack::new(self, program)?;
        // Check if the program ID exists in the process.
        match self.contains_program(program.id()) {
            // If the program already exists, ensure it is the same and return.
            true => {
                // Retrieve the existing stack.
                let existing_stack = self.get_stack(program.id())?;
                // Ensure the stacks are the same.
                match existing_stack == &stack {
                    true => Ok(()),
                    false => bail!("Program already exists but differs in its contents."),
                }
            }
            // Otherwise, insert the program stack.
            false => {
                // Add the stack to the process.
                self.stacks.insert(*program.id(), stack);
                // Return success.
                Ok(())
            }
        }
    }
}
