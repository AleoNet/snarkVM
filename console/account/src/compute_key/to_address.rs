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

impl<N: Network> ComputeKey<N> {
    /// Returns the address corresponding to the compute key.
    pub fn to_address(&self) -> Address<N> {
        // Compute pk_prf := G^sk_prf.
        let pk_prf = N::g_scalar_multiply(&self.sk_prf);
        // Compute the address := pk_sig + pr_sig + pk_prf.
        Address::new(self.pk_sig + self.pr_sig + pk_prf)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network::Testnet3;

    type CurrentNetwork = Testnet3;

    const ITERATIONS: u64 = 1000;

    #[test]
    fn test_try_from() -> Result<()> {
        let mut rng = TestRng::default();

        for _ in 0..ITERATIONS {
            // Sample a new compute key and address.
            let private_key = PrivateKey::<CurrentNetwork>::new(&mut rng)?;
            let compute_key = ComputeKey::try_from(private_key)?;
            let address = Address::try_from(private_key)?;

            assert_eq!(address, compute_key.to_address());
        }
        Ok(())
    }
}
