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

use snarkvm_curves::{bls12_377::Bls12_377, traits::PairingEngine};
use snarkvm_fields::PrimeField;
use snarkvm_gadgets::{
    traits::fields::FieldGadget,
    utilities::{alloc::AllocGadget, eq::EqGadget},
};
use snarkvm_nonnative::NonNativeFieldVar;
use snarkvm_r1cs::{ConstraintSystem, TestConstraintSystem};

use rand::{RngCore, SeedableRng};
use rand_xorshift::XorShiftRng;

#[cfg(not(ci))]
const NUM_REPETITIONS: usize = 100;
#[cfg(ci)]
const NUM_REPETITIONS: usize = 1;

#[cfg(not(ci))]
const TEST_COUNT: usize = 100;
#[cfg(ci)]
const TEST_COUNT: usize = 1;

fn allocation_test<TargetField: PrimeField, BaseField: PrimeField, CS: ConstraintSystem<BaseField>, R: RngCore>(
    mut cs: CS,
    rng: &mut R,
) {
    let a_native = TargetField::rand(rng);
    let a = NonNativeFieldVar::<TargetField, BaseField>::alloc(cs.ns(|| "alloc_a"), || Ok(a_native)).unwrap();

    let a_actual = a.value().unwrap();
    let a_expected = a_native;
    assert!(
        a_actual.eq(&a_expected),
        "allocated value does not equal the expected value"
    );
}

fn addition_test<TargetField: PrimeField, BaseField: PrimeField, CS: ConstraintSystem<BaseField>, R: RngCore>(
    mut cs: CS,
    rng: &mut R,
) {
    let a_native = TargetField::rand(rng);
    let a = NonNativeFieldVar::<TargetField, BaseField>::alloc(cs.ns(|| "alloc_a"), || Ok(a_native)).unwrap();

    let b_native = TargetField::rand(rng);
    let b = NonNativeFieldVar::<TargetField, BaseField>::alloc(cs.ns(|| "alloc_b"), || Ok(b_native)).unwrap();

    let a_plus_b = a.add(cs.ns(|| "a_plus_b"), &b).unwrap();

    let a_plus_b_actual = a_plus_b.value().unwrap();
    let a_plus_b_expected = a_native + &b_native;
    assert!(a_plus_b_actual.eq(&a_plus_b_expected), "a + b failed");
}

fn multiplication_test<TargetField: PrimeField, BaseField: PrimeField, CS: ConstraintSystem<BaseField>, R: RngCore>(
    mut cs: CS,
    rng: &mut R,
) {
    let a_native = TargetField::rand(rng);
    let a = NonNativeFieldVar::<TargetField, BaseField>::alloc(cs.ns(|| "alloc_a"), || Ok(a_native)).unwrap();

    let b_native = TargetField::rand(rng);
    let b = NonNativeFieldVar::<TargetField, BaseField>::alloc(cs.ns(|| "alloc_b"), || Ok(b_native)).unwrap();

    let a_times_b = a.mul(cs.ns(|| "a_times_b"), &b).unwrap();

    let a_times_b_actual = a_times_b.value().unwrap();
    let a_times_b_expected = a_native * &b_native;

    assert!(
        a_times_b_actual.eq(&a_times_b_expected),
        "a_times_b = {:?}, a_times_b_actual = {:?}, a_times_b_expected = {:?}",
        a_times_b,
        a_times_b_actual.into_repr().as_ref(),
        a_times_b_expected.into_repr().as_ref()
    );
}

fn equality_test<TargetField: PrimeField, BaseField: PrimeField, CS: ConstraintSystem<BaseField>, R: RngCore>(
    mut cs: CS,
    rng: &mut R,
) {
    let a_native = TargetField::rand(rng);
    let a = NonNativeFieldVar::<TargetField, BaseField>::alloc(cs.ns(|| "alloc_a"), || Ok(a_native)).unwrap();

    let b_native = TargetField::rand(rng);
    let b = NonNativeFieldVar::<TargetField, BaseField>::alloc(cs.ns(|| "alloc_b"), || Ok(b_native)).unwrap();

    let a_times_b = a.mul(cs.ns(|| "a_times_b"), &b).unwrap();

    let a_times_b_expected = a_native * &b_native;
    let a_times_b_expected_gadget =
        NonNativeFieldVar::<TargetField, BaseField>::alloc(cs.ns(|| "alloc a * b"), || Ok(a_times_b_expected)).unwrap();

    a_times_b
        .enforce_equal(cs.ns(|| "enforce_equal"), &a_times_b_expected_gadget)
        .unwrap();
}

fn edge_cases_test<TargetField: PrimeField, BaseField: PrimeField, CS: ConstraintSystem<BaseField>, R: RngCore>(
    mut cs: CS,
    rng: &mut R,
) {
    let zero_native = TargetField::zero();
    let zero = NonNativeFieldVar::<TargetField, BaseField>::zero(cs.ns(|| "zero")).unwrap();
    let one = NonNativeFieldVar::<TargetField, BaseField>::one(cs.ns(|| "one")).unwrap();

    let a_native = TargetField::rand(rng);
    let minus_a_native = TargetField::zero() - &a_native;
    let a = NonNativeFieldVar::<TargetField, BaseField>::alloc(cs.ns(|| "alloc_a"), || Ok(a_native)).unwrap();

    let a_plus_zero = a.add(cs.ns(|| "a_plus_zero"), &zero).unwrap();
    let a_minus_zero = a.sub(cs.ns(|| "a_minus_zero"), &zero).unwrap();
    let zero_minus_a = zero.sub(cs.ns(|| "zero_minus_a"), &a).unwrap();
    let a_times_zero = a.mul(cs.ns(|| "a_times_zero"), &zero).unwrap();

    let zero_plus_a = zero.add(cs.ns(|| "zero_plus_a"), &a).unwrap();
    let zero_times_a = zero.mul(cs.ns(|| "zero_times_a"), &a).unwrap();

    let a_times_one = a.mul(cs.ns(|| "a_times_one"), &one).unwrap();
    let one_times_a = one.mul(cs.ns(|| "one_times_a"), &a).unwrap();

    let a_plus_zero_native = a_plus_zero.value().unwrap();
    let a_minus_zero_native = a_minus_zero.value().unwrap();
    let zero_minus_a_native = zero_minus_a.value().unwrap();
    let a_times_zero_native = a_times_zero.value().unwrap();
    let zero_plus_a_native = zero_plus_a.value().unwrap();
    let zero_times_a_native = zero_times_a.value().unwrap();
    let a_times_one_native = a_times_one.value().unwrap();
    let one_times_a_native = one_times_a.value().unwrap();

    assert!(
        a_plus_zero_native.eq(&a_native),
        "a_plus_zero = {:?}, a = {:?}",
        a_plus_zero_native.into_repr().as_ref(),
        a_native.into_repr().as_ref()
    );
    assert!(
        a_minus_zero_native.eq(&a_native),
        "a_minus_zero = {:?}, a = {:?}",
        a_minus_zero_native.into_repr().as_ref(),
        a_native.into_repr().as_ref()
    );

    assert!(
        zero_minus_a_native.eq(&minus_a_native),
        "zero_minus_a = {:?}, minus_a = {:?}",
        zero_minus_a_native.into_repr().as_ref(),
        minus_a_native.into_repr().as_ref()
    );
    assert!(
        a_times_zero_native.eq(&zero_native),
        "a_times_zero = {:?}, zero = {:?}",
        a_times_zero_native.into_repr().as_ref(),
        zero_native.into_repr().as_ref()
    );
    assert!(
        zero_plus_a_native.eq(&a_native),
        "zero_plus_a = {:?}, a = {:?}",
        zero_plus_a_native.into_repr().as_ref(),
        a_native.into_repr().as_ref()
    );
    assert!(
        zero_times_a_native.eq(&zero_native),
        "zero_times_a = {:?}, zero = {:?}",
        zero_times_a_native.into_repr().as_ref(),
        zero_native.into_repr().as_ref()
    );
    assert!(
        a_times_one_native.eq(&a_native),
        "a_times_one = {:?}, a = {:?}",
        a_times_one_native.into_repr().as_ref(),
        a_native.into_repr().as_ref()
    );
    assert!(
        one_times_a_native.eq(&a_native),
        "one_times_a = {:?}, a = {:?}",
        one_times_a_native.into_repr().as_ref(),
        a_native.into_repr().as_ref()
    );
}

fn distribution_law_test<
    TargetField: PrimeField,
    BaseField: PrimeField,
    CS: ConstraintSystem<BaseField>,
    R: RngCore,
>(
    mut cs: CS,
    rng: &mut R,
) {
    let a_native = TargetField::rand(rng);
    let b_native = TargetField::rand(rng);
    let c_native = TargetField::rand(rng);

    let a_plus_b_native = a_native + &b_native;
    let a_times_c_native = a_native * &c_native;
    let b_times_c_native = b_native * &c_native;
    let a_plus_b_times_c_native = a_plus_b_native * &c_native;
    let a_times_c_plus_b_times_c_native = a_times_c_native + &b_times_c_native;

    assert!(
        a_plus_b_times_c_native.eq(&a_times_c_plus_b_times_c_native),
        "(a + b) * c doesn't equal (a * c) + (b * c)"
    );

    let a = NonNativeFieldVar::<TargetField, BaseField>::alloc(cs.ns(|| "a"), || Ok(a_native)).unwrap();
    let b = NonNativeFieldVar::<TargetField, BaseField>::alloc(cs.ns(|| "b"), || Ok(b_native)).unwrap();
    let c = NonNativeFieldVar::<TargetField, BaseField>::alloc(cs.ns(|| "c"), || Ok(c_native)).unwrap();

    let a_plus_b = a.add(cs.ns(|| "a_plus_b"), &b).unwrap();
    let a_times_c = a.mul(cs.ns(|| "a_times_c"), &c).unwrap();
    let b_times_c = b.mul(cs.ns(|| "b_times_c"), &c).unwrap();
    let a_plus_b_times_c = a_plus_b.mul(cs.ns(|| "a_plus_b_times_c"), &c).unwrap();
    let a_times_c_plus_b_times_c = a_times_c.add(cs.ns(|| "a_times_c_plus_b_times_c"), &b_times_c).unwrap();

    assert!(a_plus_b.value().unwrap().eq(&a_plus_b_native), "a + b doesn't match");
    assert!(a_times_c.value().unwrap().eq(&a_times_c_native), "a * c doesn't match");
    assert!(b_times_c.value().unwrap().eq(&b_times_c_native), "b * c doesn't match");
    assert!(
        a_plus_b_times_c.value().unwrap().eq(&a_plus_b_times_c_native),
        "(a + b) * c doesn't match"
    );
    assert!(
        a_times_c_plus_b_times_c
            .value()
            .unwrap()
            .eq(&a_times_c_plus_b_times_c_native),
        "(a * c) + (b * c) doesn't match"
    );
    assert!(
        a_plus_b_times_c_native.eq(&a_times_c_plus_b_times_c_native),
        "(a + b) * c != (a * c) + (b * c)"
    );
}

fn randomized_arithmetic_test<
    TargetField: PrimeField,
    BaseField: PrimeField,
    CS: ConstraintSystem<BaseField>,
    R: RngCore,
>(
    mut cs: CS,
    rng: &mut R,
) {
    let mut operations: Vec<u32> = Vec::new();
    for _ in 0..TEST_COUNT {
        operations.push(rng.next_u32() % 3);
    }

    let mut num_native = TargetField::rand(rng);
    let mut num =
        NonNativeFieldVar::<TargetField, BaseField>::alloc(cs.ns(|| "initial num"), || Ok(num_native)).unwrap();
    for (i, op) in operations.iter().enumerate() {
        let next_native = TargetField::rand(rng);
        let next = NonNativeFieldVar::<TargetField, BaseField>::alloc(
            cs.ns(|| format!("next num for repetition_{}", i)),
            || Ok(next_native),
        )
        .unwrap();
        match op {
            0 => {
                num_native += &next_native;
                num.add_in_place(cs.ns(|| format!("num_add_next_{}", i)), &next)
                    .unwrap();
            }
            1 => {
                num_native *= &next_native;
                num.mul_in_place(cs.ns(|| format!("num_mul_next_{}", i)), &next)
                    .unwrap();
            }
            2 => {
                num_native -= &next_native;
                num.sub_in_place(cs.ns(|| format!("num_sub_next_{}", i)), &next)
                    .unwrap();
            }
            _ => (),
        };

        assert!(num.value().unwrap().eq(&num_native), "randomized arithmetic failed:");
    }
}

fn addition_stress_test<TargetField: PrimeField, BaseField: PrimeField, CS: ConstraintSystem<BaseField>, R: RngCore>(
    mut cs: CS,
    rng: &mut R,
) {
    let mut num_native = TargetField::rand(rng);
    let mut num =
        NonNativeFieldVar::<TargetField, BaseField>::alloc(cs.ns(|| "initial num"), || Ok(num_native)).unwrap();
    for i in 0..TEST_COUNT {
        let next_native = TargetField::rand(rng);
        let next = NonNativeFieldVar::<TargetField, BaseField>::alloc(
            cs.ns(|| format!("next num for repetition_{}", i)),
            || Ok(next_native),
        )
        .unwrap();
        num_native += &next_native;
        num = num.add(cs.ns(|| format!("num_add_next_{}", i)), &next).unwrap();

        assert!(num.value().unwrap().eq(&num_native));
    }
}

fn multiplication_stress_test<
    TargetField: PrimeField,
    BaseField: PrimeField,
    CS: ConstraintSystem<BaseField>,
    R: RngCore,
>(
    mut cs: CS,
    rng: &mut R,
) {
    let mut num_native = TargetField::rand(rng);
    let mut num =
        NonNativeFieldVar::<TargetField, BaseField>::alloc(cs.ns(|| "initial num"), || Ok(num_native)).unwrap();
    for i in 0..TEST_COUNT {
        let next_native = TargetField::rand(rng);
        let next = NonNativeFieldVar::<TargetField, BaseField>::alloc(
            cs.ns(|| format!("next num for repetition_{}", i)),
            || Ok(next_native),
        )
        .unwrap();
        num_native *= &next_native;
        num = num.mul(cs.ns(|| format!("num_mul_next_{}", i)), &next).unwrap();

        assert!(num.value().unwrap().eq(&num_native));
    }
}

fn mul_and_add_stress_test<
    TargetField: PrimeField,
    BaseField: PrimeField,
    CS: ConstraintSystem<BaseField>,
    R: RngCore,
>(
    mut cs: CS,
    rng: &mut R,
) {
    let mut num_native = TargetField::rand(rng);
    let mut num =
        NonNativeFieldVar::<TargetField, BaseField>::alloc(cs.ns(|| "initial num"), || Ok(num_native)).unwrap();
    for i in 0..TEST_COUNT {
        let next_add_native = TargetField::rand(rng);
        let next_add = NonNativeFieldVar::<TargetField, BaseField>::alloc(
            cs.ns(|| format!("next to add num for repetition_{}", i)),
            || Ok(next_add_native),
        )
        .unwrap();
        let next_mul_native = TargetField::rand(rng);
        let next_mul = NonNativeFieldVar::<TargetField, BaseField>::alloc(
            cs.ns(|| format!("next to mul num for repetition_{}", i)),
            || Ok(next_mul_native),
        )
        .unwrap();

        num_native = num_native * &next_mul_native + &next_add_native;

        num = num.mul(cs.ns(|| format!("num_mul_next_{}", i)), &next_mul).unwrap();
        num = num.add(cs.ns(|| format!("num_add_next_{}", i)), &next_add).unwrap();

        assert!(num.value().unwrap().eq(&num_native));
    }
}

fn square_mul_add_stress_test<
    TargetField: PrimeField,
    BaseField: PrimeField,
    CS: ConstraintSystem<BaseField>,
    R: RngCore,
>(
    mut cs: CS,
    rng: &mut R,
) {
    let mut num_native = TargetField::rand(rng);
    let mut num =
        NonNativeFieldVar::<TargetField, BaseField>::alloc(cs.ns(|| "initial num"), || Ok(num_native)).unwrap();
    for i in 0..TEST_COUNT {
        let next_add_native = TargetField::rand(rng);
        let next_add = NonNativeFieldVar::<TargetField, BaseField>::alloc(
            cs.ns(|| format!("next to add num for repetition_{}", i)),
            || Ok(next_add_native),
        )
        .unwrap();
        let next_mul_native = TargetField::rand(rng);
        let next_mul = NonNativeFieldVar::<TargetField, BaseField>::alloc(
            cs.ns(|| format!("next to mul num for repetition_{}", i)),
            || Ok(next_mul_native),
        )
        .unwrap();

        num_native = num_native * &num_native * &next_mul_native + &next_add_native;

        let num_squared = num.mul(cs.ns(|| format!("num_squared_{}", i)), &num).unwrap();
        let num_squared_times_next_mul = num_squared
            .mul(cs.ns(|| format!("num_mul_next_{}", i)), &next_mul)
            .unwrap();
        num = num_squared_times_next_mul
            .add(cs.ns(|| format!("num_add_next_{}", i)), &next_add)
            .unwrap();

        assert!(num.value().unwrap().eq(&num_native));
    }
}

fn double_stress_test_1<TargetField: PrimeField, BaseField: PrimeField, CS: ConstraintSystem<BaseField>, R: RngCore>(
    mut cs: CS,
    rng: &mut R,
) {
    let mut num_native = TargetField::rand(rng);
    let mut num =
        NonNativeFieldVar::<TargetField, BaseField>::alloc(cs.ns(|| "initial num"), || Ok(num_native)).unwrap();
    // Add to at least BaseField::size_in_bits() to ensure that we teat the overflowing
    for i in 0..TEST_COUNT + BaseField::size_in_bits() {
        // double
        num_native = num_native + &num_native;
        num = num.double(cs.ns(|| format!("num_double_{}", i))).unwrap();

        assert!(num.value().unwrap().eq(&num_native), "result incorrect");
    }
}

fn double_stress_test_2<TargetField: PrimeField, BaseField: PrimeField, CS: ConstraintSystem<BaseField>, R: RngCore>(
    mut cs: CS,
    rng: &mut R,
) {
    let mut num_native = TargetField::rand(rng);
    let mut num =
        NonNativeFieldVar::<TargetField, BaseField>::alloc(cs.ns(|| "initial num"), || Ok(num_native)).unwrap();
    for i in 0..TEST_COUNT {
        // double
        num_native = num_native + &num_native;
        num = num.double(cs.ns(|| format!("num_double_{}", i))).unwrap();

        assert!(num.value().unwrap().eq(&num_native));

        // square
        let num_square_native = num_native * &num_native;
        let num_square = num.mul(cs.ns(|| format!("num_squared_{}", i)), &num).unwrap();
        assert!(num_square.value().unwrap().eq(&num_square_native));
    }
}

fn double_stress_test_3<TargetField: PrimeField, BaseField: PrimeField, CS: ConstraintSystem<BaseField>, R: RngCore>(
    mut cs: CS,
    rng: &mut R,
) {
    let mut num_native = TargetField::rand(rng);
    let mut num =
        NonNativeFieldVar::<TargetField, BaseField>::alloc(cs.ns(|| "initial num"), || Ok(num_native)).unwrap();
    for i in 0..TEST_COUNT {
        // double
        num_native = num_native + &num_native;
        num = num.double(cs.ns(|| format!("num_double_{}", i))).unwrap();

        assert!(num.value().unwrap().eq(&num_native));

        // square
        let num_square_native = num_native * &num_native;
        let num_square = num.mul(cs.ns(|| format!("num_squared_{}", i)), &num).unwrap();
        let num_square_native_gadget = NonNativeFieldVar::<TargetField, BaseField>::alloc(
            cs.ns(|| format!("repetition_{}: alloc_native num", i)),
            || Ok(num_square_native),
        )
        .unwrap();

        num_square
            .enforce_equal(cs.ns(|| format!("enforce_equal_{}", i)), &num_square_native_gadget)
            .unwrap();
    }
}

fn inverse_stress_test<TargetField: PrimeField, BaseField: PrimeField, CS: ConstraintSystem<BaseField>, R: RngCore>(
    mut cs: CS,
    rng: &mut R,
) {
    for i in 0..TEST_COUNT {
        let num_native = TargetField::rand(rng);
        let num = NonNativeFieldVar::<TargetField, BaseField>::alloc(cs.ns(|| format!("num_{}", i)), || Ok(num_native))
            .unwrap();

        if num_native == TargetField::zero() {
            continue;
        }

        let num_native_inverse = num_native.inverse().unwrap();
        let num_inverse = num.inverse(cs.ns(|| format!("inverse_{}", i))).unwrap();

        assert!(num_inverse.value().unwrap().eq(&num_native_inverse));
    }
}

macro_rules! nonnative_test_individual {
    ($test_method:ident, $test_name:ident, $test_target_field:ty, $test_base_field:ty) => {
        paste::item! {
            #[test]
            fn [<$test_method _ $test_name:lower>]() {
                let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

                for i in 0..NUM_REPETITIONS {
                    let mut cs = TestConstraintSystem::<$test_base_field>::new();
                    $test_method::<$test_target_field, $test_base_field, _, _>(cs.ns(|| format!("test_{}", i)), &mut rng);
                    assert!(cs.is_satisfied());
                }
            }
        }
    };
}

macro_rules! nonnative_test {
    ($test_name:ident, $test_target_field:ty, $test_base_field:ty) => {
        nonnative_test_individual!(allocation_test, $test_name, $test_target_field, $test_base_field);
        nonnative_test_individual!(addition_test, $test_name, $test_target_field, $test_base_field);
        nonnative_test_individual!(
            multiplication_test,
            $test_name,
            $test_target_field,
            $test_base_field
        );
        nonnative_test_individual!(equality_test, $test_name, $test_target_field, $test_base_field);
        nonnative_test_individual!(edge_cases_test, $test_name, $test_target_field, $test_base_field);
        nonnative_test_individual!(
            distribution_law_test,
            $test_name,
            $test_target_field,
            $test_base_field
        );
        nonnative_test_individual!(
            randomized_arithmetic_test,
            $test_name,
            $test_target_field,
            $test_base_field
        );
        nonnative_test_individual!(
            addition_stress_test,
            $test_name,
            $test_target_field,
            $test_base_field
        );
        nonnative_test_individual!(
            multiplication_stress_test,
            $test_name,
            $test_target_field,
            $test_base_field
        );
        nonnative_test_individual!(
            mul_and_add_stress_test,
            $test_name,
            $test_target_field,
            $test_base_field
        );
        nonnative_test_individual!(
            square_mul_add_stress_test,
            $test_name,
            $test_target_field,
            $test_base_field
        );
        nonnative_test_individual!(
            double_stress_test_1,
            $test_name,
            $test_target_field,
            $test_base_field
        );
        nonnative_test_individual!(
            double_stress_test_2,
            $test_name,
            $test_target_field,
            $test_base_field
        );
        nonnative_test_individual!(
            double_stress_test_3,
            $test_name,
            $test_target_field,
            $test_base_field
        );
        nonnative_test_individual!(
            inverse_stress_test,
            $test_name,
            $test_target_field,
            $test_base_field
        );
    };
}

nonnative_test! {
    BLS12,
    <Bls12_377 as PairingEngine>::Fq,
    <Bls12_377 as PairingEngine>::Fr
}
