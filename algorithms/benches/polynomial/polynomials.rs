// Copyright (C) 2019-2023 Aleo Systems Inc.
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

use snarkvm_algorithms::fft::{polynomial::DensePolynomial, EvaluationDomain};
use snarkvm_curves::{bls12_377::Fr as Fr377, edwards_bls12::Fr as FrEdwardsBls12};
use snarkvm_utilities::{TestRng, Uniform};

use criterion::Criterion;

#[macro_use]
extern crate criterion;

// Bench polynomial addition for bls12
fn dense_polynomial_addition_bls12(c: &mut Criterion) {
    let mut rng = TestRng::default();
    for size in 1..10 {
        let domain_size = 1 << size;
        let poly_1 = DensePolynomial::<FrEdwardsBls12>::rand(domain_size - 1, &mut rng);
        let poly_2 = DensePolynomial::<FrEdwardsBls12>::rand(domain_size - 1, &mut rng);
        c.bench_function(&format!("Dense polynomial addition using BLS12 field with domain size ({size})"), |b| {
            b.iter(|| &poly_1 + &poly_2)
        });
    }
}

// Bench polynomial addition for bls12-377
fn dense_polynomial_addition_bls12_377(c: &mut Criterion) {
    let mut rng = TestRng::default();
    for size in 1..10 {
        let domain_size = 1 << size;
        let poly_1 = DensePolynomial::<Fr377>::rand(domain_size - 1, &mut rng);
        let poly_2 = DensePolynomial::<Fr377>::rand(domain_size - 1, &mut rng);
        c.bench_function(&format!("Dense polynomial addition using BLS12-377 field with domain size ({size})"), |b| {
            b.iter(|| &poly_1 + &poly_2)
        });
    }
}

// Bench polynomial multiplication for bls12
fn dense_polynomial_multiplication_bls12(c: &mut Criterion) {
    let mut rng = TestRng::default();
    for size in 1..10 {
        let domain_size = 1 << size;
        let poly_1 = DensePolynomial::<FrEdwardsBls12>::rand(domain_size - 1, &mut rng);
        let poly_2 = DensePolynomial::<FrEdwardsBls12>::rand(domain_size - 1, &mut rng);
        c.bench_function(
            &format!("Dense polynomial multiplication using BLS12 field with domain size ({size})"),
            |b| b.iter(|| &poly_1 * &poly_2),
        );
    }
}

// Bench polynomial evaluation for bls12
fn dense_polynomial_evaluation_bls12(c: &mut Criterion) {
    let mut rng = TestRng::default();
    let field_element = FrEdwardsBls12::rand(&mut rng);
    for size in 1..10 {
        let domain_size = 1 << size;
        let polynomial = DensePolynomial::<FrEdwardsBls12>::rand(domain_size - 1, &mut rng);
        c.bench_function(&format!("Dense polynomial evaluation using BLS12 field with domain size ({size})"), |b| {
            b.iter(|| polynomial.evaluate(field_element))
        });
    }
}

// Bench polynomial evaluation for bls12-377
fn dense_polynomial_evaluation_bls12_377(c: &mut Criterion) {
    let mut rng = TestRng::default();
    let field_element = Fr377::rand(&mut rng);
    for size in 1..10 {
        let domain_size = 1 << size;
        let polynomial = DensePolynomial::<Fr377>::rand(domain_size - 1, &mut rng);
        c.bench_function(&format!("Dense polynomial evaluation using BLS12 field with domain size ({size})"), |b| {
            b.iter(|| polynomial.evaluate(field_element))
        });
    }
}

// Bench Lagrange coefficient evaluation
fn bench_lagrange_coefficient_evaluation_bls_12(c: &mut Criterion) {
    let mut rng = TestRng::default();
    for size in 1..10 {
        let domain_size = 1 << size;
        let domain = EvaluationDomain::<FrEdwardsBls12>::new(domain_size).unwrap();
        // Get random point & lagrange coefficients
        let random_point = FrEdwardsBls12::rand(&mut rng);
        c.bench_function(&format!("Dense polynomial evaluation using BLS12 field with domain size ({size})"), |b| {
            b.iter(|| domain.evaluate_all_lagrange_coefficients(random_point))
        });
    }
}

// Bench Lagrange coefficient evaluation
fn bench_lagrange_coefficient_evaluation_bls_12_377(c: &mut Criterion) {
    let mut rng = TestRng::default();
    for size in 1..10 {
        let domain_size = 1 << size;
        let domain = EvaluationDomain::<Fr377>::new(domain_size).unwrap();
        // Get random point & lagrange coefficients
        let random_point = Fr377::rand(&mut rng);
        c.bench_function(&format!("Dense polynomial evaluation using BLS12 field with domain size ({size})"), |b| {
            b.iter(|| domain.evaluate_all_lagrange_coefficients(random_point))
        });
    }
}

criterion_group! {
    name = polynomial_group;
    config = Criterion::default().sample_size(10);
    targets = dense_polynomial_addition_bls12, dense_polynomial_addition_bls12_377, dense_polynomial_evaluation_bls12, dense_polynomial_evaluation_bls12_377, dense_polynomial_multiplication_bls12, bench_lagrange_coefficient_evaluation_bls_12, bench_lagrange_coefficient_evaluation_bls_12_377
}

criterion_main!(polynomial_group);
