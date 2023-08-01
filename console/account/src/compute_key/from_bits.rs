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

impl<N: Network> FromBits for ComputeKey<N> {
    /// Initializes a new compute key from a list of **little-endian** bits.
    fn from_bits_le(bits_le: &[bool]) -> Result<Self> {
        let group_size_in_bits = Group::<N>::size_in_bits();
        let scalar_size_in_bits = Scalar::<N>::size_in_bits();
        let (pk_sig_start, pk_sig_end) = (0, group_size_in_bits);
        let (pr_sig_start, pr_sig_end) = (pk_sig_end, pk_sig_end + group_size_in_bits);
        let (sk_prf_start, sk_prf_end) = (pr_sig_end, pr_sig_end + scalar_size_in_bits);
        Ok(Self {
            pk_sig: Group::from_bits_le(&bits_le[pk_sig_start..pk_sig_end])?,
            pr_sig: Group::from_bits_le(&bits_le[pr_sig_start..pr_sig_end])?,
            sk_prf: Scalar::from_bits_le(&bits_le[sk_prf_start..sk_prf_end])?,
        })
    }

    /// Initializes a new compute key from a list of **big-endian** bits.
    fn from_bits_be(bits_be: &[bool]) -> Result<Self> {
        let group_size_in_bits = Group::<N>::size_in_bits();
        let scalar_size_in_bits = Scalar::<N>::size_in_bits();
        let (pk_sig_start, pk_sig_end) = (0, group_size_in_bits);
        let (pr_sig_start, pr_sig_end) = (pk_sig_end, pk_sig_end + group_size_in_bits);
        let (sk_prf_start, sk_prf_end) = (pr_sig_end, pr_sig_end + scalar_size_in_bits);
        Ok(Self {
            pk_sig: Group::from_bits_be(&bits_be[pk_sig_start..pk_sig_end])?,
            pr_sig: Group::from_bits_be(&bits_be[pr_sig_start..pr_sig_end])?,
            sk_prf: Scalar::from_bits_be(&bits_be[sk_prf_start..sk_prf_end])?,
        })
    }
}

#[cfg(test)]
mod tests {

    // TODO
}
