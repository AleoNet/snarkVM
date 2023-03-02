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

impl<N: Network, const VARIANT: u8> Stack<N> {
    /// Evaluates the finalize operation.
    #[inline]
    pub fn evaluate<A: circuit::Aleo<Network = N>>(
        &self,
        finalize_operation: &FinalizeOperation<N, VARIANT>,
        registers: &mut Registers<N, A>,
    ) -> Result<()> {
        // Ensure the number of operands is correct.
        if finalize_operation.operands().len() > N::MAX_INPUTS {
            bail!(
                "'{}' expects <= {} operands, found {} operands",
                Self::opcode(),
                N::MAX_INPUTS,
                finalize_operation.operands().len()
            )
        }

        // Load the operands values.
        let _inputs: Vec<_> =
            finalize_operation.operands().iter().map(|operand| registers.load(&self, operand)).try_collect()?;

        // Finalize the inputs.
        match VARIANT {
            0 => {}
            _ => bail!("Invalid 'finalize' variant: {VARIANT}"),
        }
        Ok(())
    }
}
