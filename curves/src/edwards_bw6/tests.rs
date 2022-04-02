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

use crate::{
    edwards_bw6::*,
    templates::twisted_edwards_extended::tests::{edwards_test, montgomery_conversion_test},
    traits::{
        tests_field::{field_serialization_test, field_test, primefield_test},
        tests_group::*,
        tests_projective::curve_tests,
        AffineCurve,
        ProjectiveCurve,
    },
};

#[test]
fn test_edwards_bw6_fr() {
    let a: Fr = rand::random();
    let b: Fr = rand::random();
    field_test(a, b);
    primefield_test::<Fr>();
    field_serialization_test::<Fr>();
}

#[test]
fn test_edwards_bw6_fq() {
    let a: Fq = rand::random();
    let b: Fq = rand::random();
    field_test(a, b);
    primefield_test::<Fq>();
    field_serialization_test::<Fq>();
}

#[test]
fn test_projective_curve() {
    curve_tests::<EdwardsProjective>();
    edwards_test::<EdwardsParameters>();
}

#[test]
fn test_projective_group() {
    for _i in 0..10 {
        let a = rand::random();
        let b = rand::random();
        projective_test::<EdwardsProjective>(a, b);
    }
}

#[test]
fn test_affine_group() {
    for _i in 0..10 {
        let a: EdwardsAffine = rand::random();
        affine_test::<EdwardsAffine>(a);
    }
}

#[test]
fn test_generator() {
    let generator = EdwardsAffine::prime_subgroup_generator();
    assert!(generator.is_on_curve());
    assert!(generator.is_in_correct_subgroup_assuming_on_curve());
}

#[test]
fn test_conversion() {
    let a: EdwardsAffine = rand::random();
    let b: EdwardsAffine = rand::random();
    assert_eq!(a.to_projective().to_affine(), a);
    assert_eq!(b.to_projective().to_affine(), b);
}

#[test]
fn test_montgomery_conversion() {
    montgomery_conversion_test::<EdwardsParameters>();
}
