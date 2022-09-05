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

use crate::traits::{AffineCurve, ProjectiveCurve};
use snarkvm_fields::Zero;
use snarkvm_utilities::rand::{test_rng, Uniform};

use std::ops::Mul;

pub const ITERATIONS: usize = 5;

fn random_addition_test<G: ProjectiveCurve>() {
    let mut rng = test_rng();

    for _ in 0..ITERATIONS {
        let a = G::rand(&mut rng);
        let b = G::rand(&mut rng);
        let c = G::rand(&mut rng);
        let a_affine = a.to_affine();
        let b_affine = b.to_affine();
        let c_affine = c.to_affine();

        // a + a should equal the doubling
        {
            let mut aplusa = a;
            aplusa.add_assign(a);

            let mut aplusamixed = a;
            aplusamixed.add_assign_mixed(&a.to_affine());

            let mut adouble = a;
            adouble.double_in_place();

            assert_eq!(aplusa, adouble);
            assert_eq!(aplusa, aplusamixed);
        }

        let mut tmp = vec![G::zero(); 6];

        // (a + b) + c
        tmp[0] = (a + b) + c;

        // a + (b + c)
        tmp[1] = a + (b + c);

        // (a + c) + b
        tmp[2] = (a + c) + b;

        // Mixed addition

        // (a + b) + c
        tmp[3] = a_affine.to_projective();
        tmp[3].add_assign_mixed(&b_affine);
        tmp[3].add_assign_mixed(&c_affine);

        // a + (b + c)
        tmp[4] = b_affine.to_projective();
        tmp[4].add_assign_mixed(&c_affine);
        tmp[4].add_assign_mixed(&a_affine);

        // (a + c) + b
        tmp[5] = a_affine.to_projective();
        tmp[5].add_assign_mixed(&c_affine);
        tmp[5].add_assign_mixed(&b_affine);

        // Comparisons
        for i in 0..6 {
            for j in 0..6 {
                if tmp[i] != tmp[j] {
                    println!("{} \n{}", tmp[i], tmp[j]);
                }
                assert_eq!(tmp[i], tmp[j], "Associativity failed {} {}", i, j);
                assert_eq!(tmp[i].to_affine(), tmp[j].to_affine(), "Associativity failed");
            }

            assert!(tmp[i] != a);
            assert!(tmp[i] != b);
            assert!(tmp[i] != c);

            assert!(a != tmp[i]);
            assert!(b != tmp[i]);
            assert!(c != tmp[i]);
        }
    }
}

fn random_multiplication_test<G: ProjectiveCurve>() {
    let mut rng = test_rng();

    for _ in 0..ITERATIONS {
        let mut a = G::rand(&mut rng);
        let mut b = G::rand(&mut rng);
        let a_affine = a.to_affine();
        let b_affine = b.to_affine();

        let s = G::ScalarField::rand(&mut rng);

        // s ( a + b )
        let mut tmp1 = a;
        tmp1.add_assign(b);
        tmp1.mul_assign(s);

        // sa + sb
        a.mul_assign(s);
        b.mul_assign(s);

        let mut tmp2 = a;
        tmp2.add_assign(b);

        // Affine multiplication
        let mut tmp3 = a_affine.mul(s);
        tmp3.add_assign(b_affine.mul(s));

        assert_eq!(tmp1, tmp2);
        assert_eq!(tmp1, tmp3);
    }
}

fn random_doubling_test<G: ProjectiveCurve>() {
    let mut rng = test_rng();

    for _ in 0..ITERATIONS {
        let mut a = G::rand(&mut rng);
        let mut b = G::rand(&mut rng);

        // 2(a + b)
        let mut tmp1 = a;
        tmp1.add_assign(b);
        tmp1.double_in_place();

        // 2a + 2b
        a.double_in_place();
        b.double_in_place();

        let mut tmp2 = a;
        tmp2.add_assign(b);

        let mut tmp3 = a;
        tmp3.add_assign_mixed(&b.to_affine());

        assert_eq!(tmp1, tmp2);
        assert_eq!(tmp1, tmp3);
    }
}

fn random_negation_test<G: ProjectiveCurve>() {
    let mut rng = test_rng();

    for _ in 0..ITERATIONS {
        let r = G::rand(&mut rng);

        let s = G::ScalarField::rand(&mut rng);
        let sneg = -s;
        assert!((s + sneg).is_zero());

        let mut t1 = r;
        t1.mul_assign(s);

        let mut t2 = r;
        t2.mul_assign(sneg);

        let mut t3 = t1;
        t3.add_assign(t2);
        println!("t3 = {}", t3);
        assert!(t3.is_zero());

        let mut t4 = t1;
        t4.add_assign_mixed(&t2.to_affine());
        assert!(t4.is_zero());

        t1 = -t1;
        assert_eq!(t1, t2);
    }
}

fn random_transformation_test<G: ProjectiveCurve>() {
    let mut rng = test_rng();

    for _ in 0..ITERATIONS {
        let g = G::rand(&mut rng);
        let g_affine = g.to_affine();
        let g_projective = g_affine.to_projective();
        assert_eq!(g, g_projective);
    }

    // Batch normalization
    for _ in 0..10 {
        let mut v = (0..ITERATIONS).map(|_| G::rand(&mut rng)).collect::<Vec<_>>();

        for i in &v {
            assert!(!i.is_normalized());
        }

        use rand::distributions::{Distribution, Uniform};
        let between = Uniform::from(0..ITERATIONS);
        // Sprinkle in some normalized points
        for _ in 0..5 {
            v[between.sample(&mut rng)] = G::zero();
        }
        for _ in 0..5 {
            let s = between.sample(&mut rng);
            v[s] = v[s].to_affine().to_projective();
        }

        let expected_v = v.iter().map(|v| v.to_affine().to_projective()).collect::<Vec<_>>();
        G::batch_normalization(&mut v);

        for i in &v {
            assert!(i.is_normalized());
        }

        assert_eq!(v, expected_v);
    }
}

pub fn curve_tests<G: ProjectiveCurve>() {
    let mut rng = test_rng();

    // Negation edge case with zero.
    {
        let z = -G::zero();
        assert!(z.is_zero());
    }

    // Doubling edge case with zero.
    {
        let mut z = -G::zero();
        z.double_in_place();
        assert!(z.is_zero());
    }

    // Addition edge cases with zero
    {
        let mut r = G::rand(&mut rng);
        let rcopy = r;
        r.add_assign(G::zero());
        assert_eq!(r, rcopy);
        r.add_assign_mixed(&G::Affine::zero());
        assert_eq!(r, rcopy);

        let mut z = G::zero();
        z.add_assign(G::zero());
        assert!(z.is_zero());
        z.add_assign_mixed(&G::Affine::zero());
        assert!(z.is_zero());

        let mut z2 = z;
        z2.add_assign(r);

        z.add_assign_mixed(&r.to_affine());

        assert_eq!(z, z2);
        assert_eq!(z, r);
    }

    // Transformations
    {
        let a = G::rand(&mut rng);
        let b = a.to_affine().to_projective();
        let c = a.to_affine().to_projective().to_affine().to_projective();
        assert_eq!(a, b);
        assert_eq!(b, c);
    }

    random_addition_test::<G>();
    random_multiplication_test::<G>();
    random_doubling_test::<G>();
    random_negation_test::<G>();
    random_transformation_test::<G>();
}
