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

impl<N: Network> Package<N> {
    /// Builds the package.
    pub fn build<A: crate::circuit::Aleo<Network = N, BaseField = N::Field>>(&self) -> Result<()> {
        // Retrieve the main program.
        let program = self.program_file.program();
        // Retrieve the program ID.
        let program_id = program.id();

        // Create the process.
        let process = Process::<N, A>::new(program.clone())?;

        // Load each function circuit.
        for function_name in program.functions().keys() {
            process.circuit_key(program_id, function_name)?;
        }

        Ok(())
    }
}
