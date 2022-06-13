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

impl<N: Network> Record<N> {
    /// Initializes a new record by encrypting the given state with a given record view key.
    pub fn encrypt(state: &State<N>, record_view_key: &Field<N>) -> Result<Self> {
        // Ensure the balance is less than or equal to 2^52.
        ensure!(state.balance().to_bits_le()[52..].iter().all(|bit| !bit), "Attempted to encrypt an invalid balance");
        // Compute the randomizers.
        let randomizers = N::hash_many_psd8(&[N::encryption_domain(), *record_view_key], 3);
        // Encrypt the owner.
        let owner = state.owner().to_x_coordinate() + randomizers[0];
        // Encrypt the balance.
        let balance = Field::<N>::from_u64(*state.balance()) + randomizers[1];

        // // Encrypt the data.
        // let data = state.data().encrypt_symmetric(&(*record_view_key * randomizers[2]))?;

        // Compute the MAC := Hash(G^r^view_key).
        let mac = N::hash_psd2(&[N::mac_domain(), *record_view_key])?;

        // Compute the randomizer for the balance commitment (i.e. HashToScalar(G^r^view_key));
        let r_bcm = N::hash_to_scalar_psd2(&[N::bcm_domain(), *record_view_key])?;
        // Compute the balance commitment := G^balance H^HashToScalar(G^r^view_key).
        let bcm = N::commit_ped64(&state.balance().to_bits_le(), &r_bcm)?;

        Ok(Self { owner, balance, data: state.data(), nonce: state.nonce(), mac, bcm })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network::Testnet3;
    use snarkvm_utilities::{test_rng, Uniform};

    type CurrentNetwork = Testnet3;

    const ITERATIONS: u64 = 100;

    /// This test sanity checks that the first 2 indices of the randomizers remain the same,
    /// even when `num_outputs` is greater than 2.
    #[test]
    fn test_randomizers_num_outputs() {
        for _ in 0..ITERATIONS {
            // Sample a random record view key.
            let record_view_key = Uniform::rand(&mut test_rng());
            // Compute the randomizers.
            let randomizers =
                CurrentNetwork::hash_many_psd8(&[CurrentNetwork::encryption_domain(), record_view_key], 2);
            // Retrieve the first and second randomizers.
            let randomizer_0 = randomizers[0];
            let randomizer_1 = randomizers[1];

            for num_outputs in 2..50 {
                // Compute the randomizers.
                let randomizers = CurrentNetwork::hash_many_psd8(
                    &[CurrentNetwork::encryption_domain(), record_view_key],
                    num_outputs,
                );
                // Ensure the first two indices of the randomizers remain the same.
                assert_eq!(randomizer_0, randomizers[0]);
                assert_eq!(randomizer_1, randomizers[1]);
            }
        }
    }
}
