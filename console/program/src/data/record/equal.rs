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

impl<N: Network, Private: Visibility<Boolean = Boolean<N>>> Eq for Record<N, Private> {}

impl<N: Network, Private: Visibility<Boolean = Boolean<N>>> PartialEq for Record<N, Private> {
    /// Returns `true` if `self` and `other` are equal.
    fn eq(&self, other: &Self) -> bool {
        *self.is_equal(other)
    }
}

impl<N: Network, Private: Visibility<Boolean = Boolean<N>>> Equal<Self> for Record<N, Private> {
    type Output = Boolean<N>;

    /// Returns `true` if `self` and `other` are equal.
    ///
    /// Note: This method does **not** check the `nonce` equality.
    fn is_equal(&self, other: &Self) -> Self::Output {
        // Recursively check each entry for equality.
        let mut equal = Boolean::new(true);
        for ((name_a, entry_a), (name_b, entry_b)) in self.data.iter().zip_eq(other.data.iter()) {
            equal = equal & name_a.is_equal(name_b) & entry_a.is_equal(entry_b);
        }

        // Check the `owner`, `gates`, `data`, and `nonce`.
        self.owner.is_equal(&other.owner)
            & self.gates.is_equal(&other.gates)
            & equal
            & self.nonce.is_equal(&other.nonce)
    }

    /// Returns `true` if `self` and `other` are *not* equal.
    ///
    /// Note: This method does **not** check the `nonce` equality.
    fn is_not_equal(&self, other: &Self) -> Self::Output {
        // Recursively check each entry for inequality.
        let mut not_equal = Boolean::new(false);
        for ((name_a, entry_a), (name_b, entry_b)) in self.data.iter().zip_eq(other.data.iter()) {
            not_equal = not_equal | name_a.is_not_equal(name_b) | entry_a.is_not_equal(entry_b);
        }

        // Check the `owner`, `gates`, `data`, and `nonce`.
        self.owner.is_not_equal(&other.owner)
            | self.gates.is_not_equal(&other.gates)
            | not_equal
            | self.nonce.is_not_equal(&other.nonce)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network::Testnet3;

    type CurrentNetwork = Testnet3;

    fn sample_record() -> Record<CurrentNetwork, Plaintext<CurrentNetwork>> {
        Record::<CurrentNetwork, Plaintext<CurrentNetwork>>::from_str(
            r"{
    owner: aleo14tlamssdmg3d0p5zmljma573jghe2q9n6wz29qf36re2glcedcpqfg4add.private,
    gates: 0u64.private,
    a: true.private,
    b: 123456789field.public,
    c: 0group.private,
    d: {
        e: true.private,
        f: 123456789field.private,
        g: 0group.private
    },
    _nonce: 0group.public
}",
        )
        .unwrap()
    }

    fn sample_mismatched_record() -> Record<CurrentNetwork, Plaintext<CurrentNetwork>> {
        Record::<CurrentNetwork, Plaintext<CurrentNetwork>>::from_str(
            r"{
    owner: aleo14tlamssdmg3d0p5zmljma573jghe2q9n6wz29qf36re2glcedcpqfg4add.private,
    gates: 0u64.private,
    a: true.public,
    b: 123456789field.public,
    c: 0group.private,
    d: {
        e: true.private,
        f: 123456789field.private,
        g: 0group.private
    },
    _nonce: 0group.public
}",
        )
        .unwrap()
    }

    fn check_is_equal() {
        // Sample the record.
        let record = sample_record();
        let mismatched_record = sample_mismatched_record();

        let candidate = record.is_equal(&record);
        assert!(*candidate);

        let candidate = record.is_equal(&mismatched_record);
        assert!(!*candidate);
    }

    fn check_is_not_equal() {
        // Sample the record.
        let record = sample_record();
        let mismatched_record = sample_mismatched_record();

        let candidate = record.is_not_equal(&mismatched_record);
        assert!(*candidate);

        let candidate = record.is_not_equal(&record);
        assert!(!*candidate);
    }

    #[test]
    fn test_is_equal() {
        check_is_equal()
    }

    #[test]
    fn test_is_not_equal() {
        check_is_not_equal()
    }
}
