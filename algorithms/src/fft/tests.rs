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

use crate::fft::domain::*;
use snarkvm_curves::{bls12_377::Bls12_377, traits::PairingEngine};
use snarkvm_fields::FftField;
use snarkvm_utilities::rand::UniformRand;

/// Test multiplying various (low degree) polynomials together and
/// comparing with naive evaluations.
#[test]
fn fft_composition() {
    fn test_fft_composition<E: PairingEngine, R: rand::Rng>(rng: &mut R) {
        for coeffs in 0..10 {
            let coeffs = 1 << coeffs;

            let mut v = vec![];
            for _ in 0..coeffs {
                v.push(E::Fr::rand(rng));
            }
            let mut v2 = v.clone();

            let domain = EvaluationDomain::<E::Fr>::new(coeffs).unwrap();
            domain.ifft_in_place(&mut v2);
            domain.fft_in_place(&mut v2);
            assert_eq!(v, v2, "ifft(fft(.)) != iden");

            domain.fft_in_place(&mut v2);
            domain.ifft_in_place(&mut v2);
            assert_eq!(v, v2, "fft(ifft(.)) != iden");

            domain.coset_ifft_in_place(&mut v2);
            domain.coset_fft_in_place(&mut v2);
            assert_eq!(v, v2, "coset_ifft(coset_fft(.)) != iden");

            domain.coset_fft_in_place(&mut v2);
            domain.coset_ifft_in_place(&mut v2);
            assert_eq!(v, v2, "coset_ifft(coset_fft(.)) != iden");
        }
    }

    let rng = &mut rand::thread_rng();

    test_fft_composition::<Bls12_377, _>(rng);
}

#[cfg(feature = "parallel")]
#[test]
fn parallel_fft_consistency() {
    use crate::fft::multicore::*;
    use snarkvm_fields::{Field, One};

    use rand::Rng;
    use std::cmp::min;

    fn serial_radix2_ifft<E: PairingEngine>(a: &mut [E::Fr], omega: E::Fr, log_n: u32) {
        serial_radix2_fft(a, omega.inverse().unwrap(), log_n);
        let domain_size_inv = E::Fr::from(a.len() as u64).inverse().unwrap();
        for coeff in a.iter_mut() {
            *coeff *= &domain_size_inv;
        }
    }

    fn serial_radix2_coset_fft<E: PairingEngine>(a: &mut [E::Fr], omega: E::Fr, log_n: u32) {
        let coset_shift = E::Fr::multiplicative_generator();
        let mut cur_pow = E::Fr::one();
        for coeff in a.iter_mut() {
            *coeff *= &cur_pow;
            cur_pow *= &coset_shift;
        }
        serial_radix2_fft(a, omega, log_n);
    }

    fn serial_radix2_coset_ifft<E: PairingEngine>(a: &mut [E::Fr], omega: E::Fr, log_n: u32) {
        serial_radix2_ifft::<E>(a, omega, log_n);
        let coset_shift = E::Fr::multiplicative_generator().inverse().unwrap();
        let mut cur_pow = E::Fr::one();
        for coeff in a.iter_mut() {
            *coeff *= &cur_pow;
            cur_pow *= &coset_shift;
        }
    }

    fn test_basic_consistency<E: PairingEngine, R: Rng>(rng: &mut R, max_coeffs: u32) {
        let worker = Worker::new();

        for _ in 0..5 {
            for log_d in 0..max_coeffs {
                let d = 1 << log_d;

                let mut v1 = (0..d).map(|_| E::Fr::rand(rng)).collect::<Vec<_>>();
                let mut v2 = v1.clone();

                let domain = EvaluationDomain::new(v1.len()).unwrap();

                for log_cpus in log_d..min(log_d + 1, 3) {
                    parallel_radix2_fft(&mut v1, &worker, domain.group_gen, log_d, log_cpus);
                    serial_radix2_fft(&mut v2, domain.group_gen, log_d);

                    assert_eq!(v1, v2);
                }
            }
        }
    }

    fn test_consistency<E: PairingEngine, R: Rng>(rng: &mut R, max_coeffs: u32) {
        for _ in 0..5 {
            for log_d in 0..max_coeffs {
                let d = 1 << log_d;

                let expected_poly = (0..d).map(|_| E::Fr::rand(rng)).collect::<Vec<_>>();
                let mut expected_vec = expected_poly.clone();
                let mut actual_vec = expected_poly.clone();

                let domain = EvaluationDomain::new(d).unwrap();

                serial_radix2_fft(&mut expected_vec, domain.group_gen, log_d);
                domain.fft_in_place(&mut actual_vec);
                assert_eq!(expected_vec, actual_vec);

                serial_radix2_ifft::<E>(&mut expected_vec, domain.group_gen, log_d);
                domain.ifft_in_place(&mut actual_vec);
                assert_eq!(expected_vec, actual_vec);
                assert_eq!(expected_vec, expected_poly);

                serial_radix2_coset_fft::<E>(&mut expected_vec, domain.group_gen, log_d);
                domain.coset_fft_in_place(&mut actual_vec);
                assert_eq!(expected_vec, actual_vec);

                serial_radix2_coset_ifft::<E>(&mut expected_vec, domain.group_gen, log_d);
                domain.coset_ifft_in_place(&mut actual_vec);
                assert_eq!(expected_vec, actual_vec);
            }
        }
    }

    let rng = &mut rand::thread_rng();

    test_basic_consistency::<Bls12_377, _>(rng, 10);
    test_consistency::<Bls12_377, _>(rng, 10);
}
