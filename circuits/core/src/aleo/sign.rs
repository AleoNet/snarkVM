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

impl<E: Environment> Aleo<E> {
    #[inline]
    pub fn sign<F: ToField>(&self, private_key: &Field<E>, message: &[F], randomizer: Scalar<E>) -> Field<E> {
        // Compute G^r.
        let g_r = self.g_scalar_multiply(&r);

        // Extract (sk_sig, r_sig).
        let (sk_sig, r_sig) = private_key;

        // Compute G^sk_sig.
        let g_sk_sig = self.g_scalar_multiply(sk_sig);

        // Compute G^r_sig.
        let g_r_sig = self.g_scalar_multiply(r_sig);

        // Compute sk_prf := RO(G^sk_sig || G^r_sig).
        let sk_prf = self.hash_to_scalar_field(&[g_sk_sig.x, g_r_sig.x]);

        // Compute G^sk_prf.
        let g_sk_prf = self.g_scalar_multiply(&sk_prf);

        // Compute G^sk_sig G^r_sig G^sk_prf.
        let public_key = g_sk_sig + g_r_sig + g_sk_prf;
    }
}

impl<E: Environment> Aleo<E> {
    fn g_scalar_multiply(&self, scalar: &Scalar<E>) -> Group<E> {
        self.bases
            .iter()
            .zip_eq(&scalar.to_bits_le())
            .fold(Group::zero(), |output, (base, bit)| Group::ternary(bit, &(output + base), &output))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_algorithms::crypto_hash::Poseidon as NativePoseidon;
    use snarkvm_circuits_environment::{assert_scope, Circuit};
    use snarkvm_utilities::{test_rng, UniformRand};

    const ITERATIONS: usize = 10;

    fn check_sign(
        mode: Mode,
        num_inputs: usize,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        let rng = &mut test_rng();
        let native = NativePoseidon::<_, RATE, OPTIMIZED_FOR_WEIGHTS>::setup();
        let circuit = Poseidon::new();

        for i in 0..ITERATIONS {
            // Prepare the preimage.
            let input = (0..num_inputs).map(|_| <Circuit as Environment>::BaseField::rand(rng)).collect::<Vec<_>>();
            let preimage = input.iter().map(|v| Field::<Circuit>::new(mode, *v)).collect::<Vec<_>>();

            // Compute the native hash.
            let expected = native.evaluate(&input);
            // Compute the circuit hash.
            Circuit::scope(format!("Poseidon {mode} {i}"), || {
                let candidate = circuit.sign(&preimage);
                assert_eq!(expected, candidate.eject_value());
                let case = format!("(mode = {mode}, num_inputs = {num_inputs})");
                assert_scope!(case, num_constants, num_public, num_private, num_constraints);
            });
        }
    }

    #[test]
    fn test_sign_constant() {
        for num_inputs in 0..=RATE {
            check_sign(Mode::Constant, num_inputs, 0, 0, 0, 0);
        }
    }

    #[test]
    fn test_sign_public() {
        check_sign(Mode::Public, 0, 0, 0, 0, 0);
        check_sign(Mode::Public, 1, 0, 0, 335, 335);
        check_sign(Mode::Public, 2, 0, 0, 340, 340);
        check_sign(Mode::Public, 3, 0, 0, 345, 345);
        check_sign(Mode::Public, 4, 0, 0, 350, 350);
        check_sign(Mode::Public, 5, 0, 0, 705, 705);
        check_sign(Mode::Public, 6, 0, 0, 705, 705);
        check_sign(Mode::Public, 7, 0, 0, 705, 705);
        check_sign(Mode::Public, 8, 0, 0, 705, 705);
        check_sign(Mode::Public, 9, 0, 0, 1060, 1060);
        check_sign(Mode::Public, 10, 0, 0, 1060, 1060);
    }

    #[test]
    fn test_sign_private() {
        check_sign(Mode::Private, 0, 0, 0, 0, 0);
        check_sign(Mode::Private, 1, 0, 0, 335, 335);
        check_sign(Mode::Private, 2, 0, 0, 340, 340);
        check_sign(Mode::Private, 3, 0, 0, 345, 345);
        check_sign(Mode::Private, 4, 0, 0, 350, 350);
        check_sign(Mode::Private, 5, 0, 0, 705, 705);
        check_sign(Mode::Private, 6, 0, 0, 705, 705);
        check_sign(Mode::Private, 7, 0, 0, 705, 705);
        check_sign(Mode::Private, 8, 0, 0, 705, 705);
        check_sign(Mode::Private, 9, 0, 0, 1060, 1060);
        check_sign(Mode::Private, 10, 0, 0, 1060, 1060);
    }
}
