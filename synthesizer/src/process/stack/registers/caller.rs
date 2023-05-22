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

impl<N: Network, A: circuit::Aleo<Network = N>> RegistersCaller<N> for Registers<N, A> {
    /// Returns the transition caller.
    #[inline]
    fn caller(&self) -> Result<Address<N>> {
        self.caller.ok_or_else(|| anyhow!("Caller address (console) is not set in the registers."))
    }

    /// Sets the transition caller.
    #[inline]
    fn set_caller(&mut self, caller: Address<N>) {
        self.caller = Some(caller);
    }

    /// Returns the transition view key.
    #[inline]
    fn tvk(&self) -> Result<Field<N>> {
        self.tvk.ok_or_else(|| anyhow!("Transition view key (console) is not set in the registers."))
    }

    /// Sets the transition view key.
    #[inline]
    fn set_tvk(&mut self, tvk: Field<N>) {
        self.tvk = Some(tvk);
    }
}

impl<N: Network, A: circuit::Aleo<Network = N>> RegistersCallerCircuit<N, A> for Registers<N, A> {
    /// Returns the transition caller, as a circuit.
    #[inline]
    fn caller_circuit(&self) -> Result<circuit::Address<A>> {
        self.caller_circuit.clone().ok_or_else(|| anyhow!("Caller address (circuit) is not set in the registers."))
    }

    /// Sets the transition caller, as a circuit.
    #[inline]
    fn set_caller_circuit(&mut self, caller_circuit: circuit::Address<A>) {
        self.caller_circuit = Some(caller_circuit);
    }

    /// Returns the transition view key, as a circuit.
    #[inline]
    fn tvk_circuit(&self) -> Result<circuit::Field<A>> {
        self.tvk_circuit.clone().ok_or_else(|| anyhow!("Transition view key (circuit) is not set in the registers."))
    }

    /// Sets the transition view key, as a circuit.
    #[inline]
    fn set_tvk_circuit(&mut self, tvk_circuit: circuit::Field<A>) {
        self.tvk_circuit = Some(tvk_circuit);
    }
}
