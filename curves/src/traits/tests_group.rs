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

use crate::{AffineCurve, ProjectiveCurve};
use snarkvm_fields::{One, Zero};
use snarkvm_utilities::rand::{test_rng, Uniform};

#[allow(clippy::eq_op)]
pub fn affine_test<G: AffineCurve>(a: G) {
    let zero = G::zero();
    let fr_zero = G::ScalarField::zero();
    let fr_one = G::ScalarField::one();
    assert!(zero == zero);
    assert!(zero.is_zero()); // true
    assert_eq!(a * fr_one, a);
    assert_eq!(a.mul(fr_zero), zero);

    // a == a
    assert!(a == a);
    assert_eq!(a.mul_by_cofactor_to_projective(), a.mul_by_cofactor());
    assert_eq!(a.mul_by_cofactor_inv().mul_by_cofactor(), a);
}

#[allow(clippy::eq_op)]
pub fn projective_test<G: ProjectiveCurve>(a: G, mut b: G) {
    let mut rng = test_rng();

    let zero = G::zero();
    let fr_zero = G::ScalarField::zero();
    let fr_one = G::ScalarField::one();
    let fr_two = fr_one + fr_one;
    assert!(zero == zero);
    assert!(zero.is_zero()); // true
    assert_eq!(a.mul(fr_one), a);
    assert_eq!(a.mul(fr_two), a + a);
    assert_eq!(a.mul(fr_zero), zero);
    assert_eq!(a.mul(fr_zero) - a, -a);
    assert_eq!(a.mul(fr_one) - a, zero);
    assert_eq!(a.mul(fr_two) - a, a);

    // a == a
    assert!(a == a);
    // a + 0 = a
    assert_eq!(a + zero, a);
    // a - 0 = a
    assert_eq!(a - zero, a);
    // a - a = 0
    assert_eq!(a - a, zero);
    // 0 - a = -a
    assert_eq!(zero - a, -a);
    // a.double() = a + a
    assert_eq!(a.double(), a + a);
    // b.double() = b + b
    assert_eq!(b.double(), b + b);
    // a + b = b + a
    assert_eq!(a + b, b + a);
    // a - b = -(b - a)
    assert_eq!(a - b, -(b - a));
    // (a + b) + a = a + (b + a)
    assert_eq!((a + b) + a, a + (b + a));
    // (a + b).double() = (a + b) + (b + a)
    assert_eq!((a + b).double(), (a + b) + (b + a));

    // Check that double_in_place and double give the same result
    let original_b = b;
    b.double_in_place();
    assert_eq!(original_b.double(), b);

    let fr_rand1 = G::ScalarField::rand(&mut rng);
    let fr_rand2 = G::ScalarField::rand(&mut rng);
    let a_rand1 = a.mul(fr_rand1);
    let a_rand2 = a.mul(fr_rand2);
    let fr_three = fr_two + fr_rand1;
    let a_two = a.mul(fr_two);
    assert_eq!(a_two, a.double(), "(a * 2)  != a.double()");
    let a_six = a.mul(fr_three * fr_two);
    assert_eq!(a_two.mul(fr_three), a_six, "(a * 2) * 3 != a * (2 * 3)");

    assert_eq!(a_rand1.mul(fr_rand2), a_rand2.mul(fr_rand1), "(a * r1) * r2 != (a * r2) * r1");
    assert_eq!(a_rand2.mul(fr_rand1), a.mul(fr_rand1 * fr_rand2), "(a * r2) * r1 != a * (r1 * r2)");
    assert_eq!(a_rand1.mul(fr_rand2), a.mul(fr_rand1 * fr_rand2), "(a * r1) * r2 != a * (r1 * r2)");
}
