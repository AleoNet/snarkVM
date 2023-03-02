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

impl<N: Network> Stack<N> {
    /// Evaluates a finalize command.
    #[inline]
    ///
    pub fn evaluate_finalize_command<P: ProgramStorage<N>>(
        &self,
        command: &Command<N>,
        store: &ProgramStore<N, P>,
        registers: &mut FinalizeRegisters<N>,
    ) -> Result<()> {
        match command {
            Command::Decrement(decrement) => self.evaluate_decrement(decrement, store, registers),
            // TODO (howardwu): Implement support for instructions (consider using a trait for `Registers::load/store`).
            // Command::Instruction(instruction) => self.evaluate_instruction(stack, registers),
            Command::Instruction(_) => bail!("Instructions in 'finalize' are not supported (yet)."),
            Command::Increment(increment) => self.evaluate_increment(increment, store, registers),
        }
    }
}
