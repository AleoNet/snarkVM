// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use super::*;

impl<N: Network> Eq for Ciphertext<N> {}

impl<N: Network> PartialEq for Ciphertext<N> {
    /// Returns `true` if `self` and `other` are equal.
    fn eq(&self, other: &Self) -> bool {
        *self.is_equal(other)
    }
}

impl<N: Network> Equal<Self> for Ciphertext<N> {
    type Output = Boolean<N>;

    /// Returns `true` if `self` and `other` are equal.
    fn is_equal(&self, other: &Self) -> Self::Output {
        // Ensure that the ciphertexts have the same number of field elements.
        if self.0.len() != other.0.len() {
            return Boolean::new(false);
        }
        // Check each field element for equality.
        let mut equal = Boolean::new(true);
        for (a, b) in self.0.iter().zip_eq(other.0.iter()) {
            equal &= a.is_equal(b);
        }
        equal
    }

    /// Returns `true` if `self` and `other` are *not* equal.
    fn is_not_equal(&self, other: &Self) -> Self::Output {
        // Check if the ciphertexts have different numbers of field elements.
        if self.0.len() != other.0.len() {
            return Boolean::new(true);
        }
        // Recursively check each member for inequality.
        let mut not_equal = Boolean::new(false);
        for (a, b) in self.0.iter().zip_eq(other.0.iter()) {
            not_equal |= a.is_not_equal(b);
        }
        not_equal
    }
}
