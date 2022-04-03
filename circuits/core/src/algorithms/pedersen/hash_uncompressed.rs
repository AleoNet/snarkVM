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

use std::borrow::Cow;

impl<E: Environment, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> Pedersen<E, NUM_WINDOWS, WINDOW_SIZE> {
    pub fn hash_uncompressed(&self, input: &[Boolean<E>]) -> Group<E> {
        let constant_false = Boolean::<E>::constant(false);

        let mut input = Cow::Borrowed(input);
        match input.len() <= WINDOW_SIZE * NUM_WINDOWS {
            // Pad the input if it is under the required parameter size.
            true => input.to_mut().resize(WINDOW_SIZE * NUM_WINDOWS, constant_false),
            // Ensure the input size is within the parameter size,
            false => E::halt("incorrect input length for pedersen hash"),
        }

        // Compute sum of h_i^{m_i} for all i.
        input
            .chunks(WINDOW_SIZE)
            .zip_eq(&self.bases)
            .flat_map(|(bits, powers)| {
                bits.iter()
                    .zip_eq(powers)
                    .map(|(bit, base)| Group::<E>::ternary(bit, base, &Group::<E>::zero()))
                    .collect::<Vec<Group<E>>>()
            })
            .fold(Group::<E>::zero(), |acc, x| acc + x)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_algorithms::{crh::PedersenCRH, CRH};
    use snarkvm_circuits_environment::{Circuit, Mode};
    use snarkvm_circuits_types::Eject;
    use snarkvm_curves::edwards_bls12::{EdwardsAffine, EdwardsProjective};
    use snarkvm_utilities::{test_rng, ToBits, UniformRand};

    const ITERATIONS: usize = 10;
    const MESSAGE: &str = "pedersen_circuit";
    const WINDOW_SIZE_MULTIPLIER: usize = 8;

    fn check_hash<const NUM_WINDOWS: usize, const WINDOW_SIZE: usize>(mode: Mode, input_value: &[bool]) {
        let native_hasher = PedersenCRH::<EdwardsProjective, { NUM_WINDOWS }, { WINDOW_SIZE }>::setup(MESSAGE);
        let circuit_hasher = Pedersen::<Circuit, { NUM_WINDOWS }, { WINDOW_SIZE }>::setup(MESSAGE);

        for i in 0..ITERATIONS {
            let native_hash: EdwardsAffine = native_hasher.hash(input_value).expect("should be able to hash input");
            let circuit_input = input_value.iter().map(|b| Boolean::<_>::new(mode, *b)).collect::<Vec<Boolean<_>>>();

            Circuit::scope(format!("Pedersen {mode} {i}"), || {
                let circuit_hash: EdwardsAffine = circuit_hasher.hash_uncompressed(&circuit_input).eject_value();
                assert_eq!(native_hash, circuit_hash);
            });
        }
    }

    fn check_hash_uncompressed<const NUM_ELEMENTS: usize, const WINDOW_SIZE: usize>(mode: Mode) {
        let rng = &mut test_rng();
        let bits = (0..NUM_ELEMENTS)
            .map(|_| <Circuit as Environment>::BaseField::rand(rng))
            .collect::<Vec<_>>()
            .iter()
            .flat_map(|el| el.to_bits_le())
            .collect::<Vec<_>>();
        check_hash::<WINDOW_SIZE, 32>(mode, &bits);
    }

    #[test]
    fn test_hash_constant() {
        check_hash_uncompressed::<1, { WINDOW_SIZE_MULTIPLIER }>(Mode::Constant);
        check_hash_uncompressed::<2, { 2 * WINDOW_SIZE_MULTIPLIER }>(Mode::Constant);
        check_hash_uncompressed::<3, { 3 * WINDOW_SIZE_MULTIPLIER }>(Mode::Constant);
        check_hash_uncompressed::<4, { 4 * WINDOW_SIZE_MULTIPLIER }>(Mode::Constant);
        check_hash_uncompressed::<5, { 5 * WINDOW_SIZE_MULTIPLIER }>(Mode::Constant);
        check_hash_uncompressed::<6, { 6 * WINDOW_SIZE_MULTIPLIER }>(Mode::Constant);
        check_hash_uncompressed::<7, { 7 * WINDOW_SIZE_MULTIPLIER }>(Mode::Constant);
        check_hash_uncompressed::<8, { 8 * WINDOW_SIZE_MULTIPLIER }>(Mode::Constant);
        check_hash_uncompressed::<9, { 9 * WINDOW_SIZE_MULTIPLIER }>(Mode::Constant);
        check_hash_uncompressed::<10, { 10 * WINDOW_SIZE_MULTIPLIER }>(Mode::Constant);
    }

    #[test]
    fn test_hash_public() {
        check_hash_uncompressed::<1, { WINDOW_SIZE_MULTIPLIER }>(Mode::Public);
        check_hash_uncompressed::<2, { 2 * WINDOW_SIZE_MULTIPLIER }>(Mode::Public);
        check_hash_uncompressed::<3, { 3 * WINDOW_SIZE_MULTIPLIER }>(Mode::Public);
        check_hash_uncompressed::<4, { 4 * WINDOW_SIZE_MULTIPLIER }>(Mode::Public);
        check_hash_uncompressed::<5, { 5 * WINDOW_SIZE_MULTIPLIER }>(Mode::Public);
        check_hash_uncompressed::<6, { 6 * WINDOW_SIZE_MULTIPLIER }>(Mode::Public);
        check_hash_uncompressed::<7, { 7 * WINDOW_SIZE_MULTIPLIER }>(Mode::Public);
        check_hash_uncompressed::<8, { 8 * WINDOW_SIZE_MULTIPLIER }>(Mode::Public);
        check_hash_uncompressed::<9, { 9 * WINDOW_SIZE_MULTIPLIER }>(Mode::Public);
        check_hash_uncompressed::<10, { 10 * WINDOW_SIZE_MULTIPLIER }>(Mode::Public);
    }

    #[test]
    fn test_hash_private() {
        check_hash_uncompressed::<1, { WINDOW_SIZE_MULTIPLIER }>(Mode::Private);
        check_hash_uncompressed::<2, { 2 * WINDOW_SIZE_MULTIPLIER }>(Mode::Private);
        check_hash_uncompressed::<3, { 3 * WINDOW_SIZE_MULTIPLIER }>(Mode::Private);
        check_hash_uncompressed::<4, { 4 * WINDOW_SIZE_MULTIPLIER }>(Mode::Private);
        check_hash_uncompressed::<5, { 5 * WINDOW_SIZE_MULTIPLIER }>(Mode::Private);
        check_hash_uncompressed::<6, { 6 * WINDOW_SIZE_MULTIPLIER }>(Mode::Private);
        check_hash_uncompressed::<7, { 7 * WINDOW_SIZE_MULTIPLIER }>(Mode::Private);
        check_hash_uncompressed::<8, { 8 * WINDOW_SIZE_MULTIPLIER }>(Mode::Private);
        check_hash_uncompressed::<9, { 9 * WINDOW_SIZE_MULTIPLIER }>(Mode::Private);
        check_hash_uncompressed::<10, { 10 * WINDOW_SIZE_MULTIPLIER }>(Mode::Private);
    }
}
