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

impl<A: Aleo, Private: Visibility<A>> Record<A, Private> {
    /// A helper method to derive the serial number from the private key and commitment.
    pub fn serial_number(private_key: PrivateKey<A>, commitment: Field<A>) -> Field<A> {
        // Compute the generator `H` as `HashToGroup(commitment)`.
        let h = A::hash_to_group_psd2(&[A::serial_number_domain(), commitment.clone()]);
        // Compute `gamma` as `sk_sig * H`.
        let gamma = h * private_key.sk_sig();
        // Compute the serial number from `gamma`.
        Self::serial_number_from_gamma(&gamma, commitment)
    }

    /// A helper method to derive the serial number from the gamma and commitment.
    pub fn serial_number_from_gamma(gamma: &Group<A>, commitment: Field<A>) -> Field<A> {
        // Compute `sn_nonce` as `Hash(COFACTOR * gamma)`.
        let sn_nonce = A::hash_to_scalar_psd2(&[A::serial_number_domain(), gamma.mul_by_cofactor().to_x_coordinate()]);
        // Compute `serial_number` as `Commit(commitment, sn_nonce)`.
        A::commit_bhp512(&(A::serial_number_domain(), commitment).to_bits_le(), &sn_nonce)
    }
}
