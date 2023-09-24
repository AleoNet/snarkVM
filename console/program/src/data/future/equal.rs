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

impl<N: Network> Eq for Future<N> {}

impl<N: Network> PartialEq for Future<N> {
    /// Returns `true` if `self` and `other` are equal.
    fn eq(&self, other: &Self) -> bool {
        *self.is_equal(other)
    }
}

impl<N: Network> Equal<Self> for Future<N> {
    type Output = Boolean<N>;

    /// Returns `true` if `self` and `other` are equal.
    fn is_equal(&self, other: &Self) -> Self::Output {
        // Recursively check each argument for equality.
        let mut equal = Boolean::new(true);
        for (argument_a, argument_b) in self.arguments.iter().zip_eq(other.arguments.iter()) {
            equal &= argument_a.is_equal(argument_b);
        }

        // Check the `program_id`, and `function_name`.
        self.program_id.is_equal(&other.program_id) & equal & self.function_name.is_equal(&other.function_name)
    }

    /// Returns `true` if `self` and `other` are *not* equal.
    fn is_not_equal(&self, other: &Self) -> Self::Output {
        // Recursively check each argument for equality.
        let mut not_equal = Boolean::new(false);
        for (argument_a, argument_b) in self.arguments.iter().zip_eq(other.arguments.iter()) {
            not_equal |= argument_a.is_not_equal(argument_b);
        }

        // Check the `program_id`, and `function_name`.
        self.program_id.is_not_equal(&other.program_id)
            | not_equal
            | self.function_name.is_not_equal(&other.function_name)
    }
}
