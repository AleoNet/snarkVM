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

use snarkvm_gadgets::{traits::fields::FieldGadget, utilities::alloc::AllocGadget};
use snarkvm_nonnative::NonNativeFieldVar;
use snarkvm_r1cs::{ConstraintSystem, TestConstraintSystem};

// TODO (raychu86): Add to_contraint_field impls.

// #[test]
// fn to_constraint_field_test() {
//     type F = snarkvm_curves::bls12_377::Fr;
//     type CF = snarkvm_curves::bls12_377::Fq;
//
//     let cs = TestConstraintSystem::<CF>::new_ref();
//
//     let a = NonNativeFieldVar::Constant(F::from(12u8));
//     let b = NonNativeFieldVar::<F, CF>::alloc(cs.ns(|| "alloc"), || Ok(F::from(6u8))).unwrap();
//
//     let b2 = &b + &b;
//     let b2 = b.double(cs.ns(|| "b_plus_b")).unwrap();
//
//     let a_to_constraint_field = a.to_constraint_field().unwrap();
//     let b2_to_constraint_field = b2.to_constraint_field().unwrap();
//
//     assert_eq!(a_to_constraint_field.len(), b2_to_constraint_field.len());
//     for (left, right) in a_to_constraint_field.iter().zip(b2_to_constraint_field.iter()) {
//         assert_eq!(left.value(), right.value());
//     }
// }
