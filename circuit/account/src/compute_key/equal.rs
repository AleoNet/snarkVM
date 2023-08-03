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

#[cfg(console)]
impl<A: Aleo> Equal<Self> for ComputeKey<A> {
    type Output = Boolean<A>;

    ///
    /// Returns `true` if `self` and `other` are equal.
    ///
    fn is_equal(&self, other: &Self) -> Self::Output {
        // Determine if this operation is constant or variable.
        match self.is_constant() && other.is_constant() {
            true => Boolean::constant(self.eject_value() == other.eject_value()),
            false => {
                self.pk_sig.is_equal(other.pk_sig())
                    & self.pr_sig.is_equal(other.pr_sig())
                    & self.sk_prf.is_equal(other.sk_prf())
            }
        }
    }

    ///
    /// Returns `true` if `self` and `other` are *not* equal.
    ///
    /// This method constructs a boolean that indicates if
    /// `self` and `other ` are *not* equal to each other.
    ///
    fn is_not_equal(&self, other: &Self) -> Self::Output {
        !self.is_equal(other)
    }
}

impl<A: Aleo> Metrics<dyn Equal<ComputeKey<A>, Output = Boolean<A>>> for ComputeKey<A> {
    type Case = (Mode, Mode);

    fn count(_case: &Self::Case) -> Count {
        todo!()
        // match case.0.is_constant() && case.1.is_constant() {
        // }
    }
}

impl<A: Aleo> OutputMode<dyn Equal<ComputeKey<A>, Output = Boolean<A>>> for ComputeKey<A> {
    type Case = (Mode, Mode);

    fn output_mode(case: &Self::Case) -> Mode {
        match case.0.is_constant() && case.1.is_constant() {
            true => Mode::Constant,
            false => Mode::Private,
        }
    }
}

#[cfg(all(test, console))]
mod tests {

    // TODO
}
