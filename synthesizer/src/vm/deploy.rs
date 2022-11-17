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

impl<N: Network, C: ConsensusStorage<N>> VM<N, C> {
    /// Deploys a program with the given program ID.
    #[inline]
    pub fn deploy<R: Rng + CryptoRng>(&self, program: &Program<N>, rng: &mut R) -> Result<Deployment<N>> {
        let timer = timer!("VM::deploy");

        // Compute the core logic.
        macro_rules! logic {
            ($process:expr, $network:path, $aleo:path) => {{
                // Prepare the program.
                let program = cast_ref!(&program as Program<$network>);

                // Compute the deployment.
                let deployment = $process.deploy::<$aleo, _>(program, rng)?;
                lap!(timer, "Compute the deployment");

                // Prepare the return.
                let deployment = cast_ref!(deployment as Deployment<N>).clone();
                lap!(timer, "Prepare the deployment");

                finish!(timer);
                // Return the deployment.
                Ok(deployment)
            }};
        }
        // Process the logic.
        process!(self, logic)
    }
}
