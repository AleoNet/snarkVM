// Copyright (C) 2019-2021 Aleo Systems Inc.
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

//
// Acknowledgements
//
// This implementation of Poseidon is entirely from Fractal's implementation
// ([COS20]: https://eprint.iacr.org/2019/1076) with small syntax changes.
//

use crate::{fiat_shamir::AlgebraicSponge, Vec};
use snarkvm_algorithms::crypto_hash::{CryptographicSponge, PoseidonDefaultParametersField};
use snarkvm_fields::PrimeField;

use snarkvm_utilities::sync::Arc;

/// The sponge for Poseidon
#[derive(Clone, Debug)]
pub struct PoseidonSponge<F: PrimeField + PoseidonDefaultParametersField> {
    /// The actual sponge element
    pub sponge: snarkvm_algorithms::crypto_hash::PoseidonSponge<F, 6, 1>,
}

impl<F: PrimeField + PoseidonDefaultParametersField> AlgebraicSponge<F> for PoseidonSponge<F> {
    fn new() -> Self {
        let params = Arc::new(F::get_default_poseidon_parameters(6, false).unwrap());
        let sponge = snarkvm_algorithms::crypto_hash::PoseidonSponge::<F>::new(&params);
        Self { sponge }
    }

    fn absorb(&mut self, elems: &[F]) {
        self.sponge.absorb(elems)
    }

    fn squeeze(&mut self, num: usize) -> Vec<F> {
        self.sponge.squeeze_field_elements(num)
    }
}
