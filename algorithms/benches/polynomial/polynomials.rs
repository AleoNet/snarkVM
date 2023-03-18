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

use snarkvm_algorithms::{
    fft::{
        evaluations::Evaluations,
        polynomial::{DensePolynomial, PolyMultiplier, Polynomial, SparsePolynomial},
        EvaluationDomain,
    },
    polycommit::{
        kzg10::KZG10,
        sonic_pc::{LabeledPolynomialWithBasis, SonicKZG10},
    },
};
use snarkvm_curves::{bls12_377::Fr as Fr377, edwards_bls12::Fr as FrEdwardsBls12};
use snarkvm_utilities::{TestRng, Uniform};

use criterion::Criterion;

#[macro_use]
extern crate criterion;

// Bench labeled polynomial and dense polynomial, polycommit functions, polynomial evaluations, PolyMultiplier.multiply (algorithms/src/fft/polynomial/multiplier.rs)

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

fn dense_polynomial_multiplication_bls12_377(c: &mut Criterion) {
    let mut rng = TestRng::default();
    for size in 1..10 {
        let domain_size = 1 << size;
        let poly_1 = DensePolynomial::<Fr377>::rand(domain_size - 1, &mut rng);
        let poly_2 = DensePolynomial::<Fr377>::rand(domain_size - 1, &mut rng);
        c.bench_function(
            &format!("Dense polynomial multiplication using BLS12-377 field with domain size ({size})"),
            |b| b.iter(|| &poly_1 * &poly_2),
        );
    }
}

/*
fn dense_polynomial_multi_multiplication_bls12(c: &mut Criterion) {
    let mut rng = TestRng::default();
    for size in (1..9).step_by(3) {
        let mut multiplier = PolyMultiplier::<FrEdwardsBls12>::new();
        let domain_size = 1 << size;
        let mut num = 0;
        for _ in (0..10).step_by(5) {
            num = 1;
            let polynomial = DensePolynomial::<FrEdwardsBls12>::rand(domain_size - 1, &mut rng);
            multiplier.add_polynomial(polynomial, 1)
        }
        c.bench_function(&format!("Multiplication of {num} multi-multiplication using BLS12 field with domain size ({size})"), |b| {
            b.iter(|| &multiplier.clone().multiply())
        });
    }
}

fn dense_polynomial_multi_multiplication_bls12_377(c: &mut Criterion) {
    let mut rng = TestRng::default();
    for size in (1..9).step_by(3) {
        let domain_size = 1 << size;
        let mut num = 0;
        for _ in (0..10).step_by(5) {
            num = 1;
            let polynomial = DensePolynomial::<Fr377>::rand(domain_size - 1, &mut rng);
            multiplier.add_polynomial(polynomial, 1)
        }
        c.bench_function(&format!("Multiplication of {num} multi-multiplication using BLS12 field with domain size ({size})"), |b| {
            b.iter(|| {
                let mut multiplier = PolyMultiplier::<Fr377>::new();
                multiplier.multiply()
            })
        });
    }
}
*/

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

/*
fn bench_poly_commit_kzg() {
    // KZG10::commit()
}

fn bench_poly_commit_sonic() {
    // SonicKZG10::commit()
}

fn bench_sonic_poly_open_with_proof() {
    //SonicKZG10::open(&commitment, &query_set, None).unwrap();
}

fn bench_poly_open_with_proof() {
    // KZG10::open(&commitment, &query_set, None).unwrap();
}

fn bench_lagrange_evaluations() {
    // let domain = EvaluationDomain::<Fr>::new(coeffs).unwrap();
    // let coeffs = domain.evaluate_all_lagrange_coefficients(*point);
}

fn bench_evaluations_with_coefficients() {
    // let domain = EvaluationDomain::<Fr>::new(coeffs).unwrap();
    // domain.evaluate_with_coeffs(&coeffs)
}
*/

criterion_group! {
    name = polynomial_group;
    config = Criterion::default().sample_size(10);
    targets = dense_polynomial_addition_bls12, dense_polynomial_addition_bls12_377, dense_polynomial_evaluation_bls12, dense_polynomial_evaluation_bls12_377, dense_polynomial_multiplication_bls12, dense_polynomial_multiplication_bls12_377
}

criterion_main!(polynomial_group);
