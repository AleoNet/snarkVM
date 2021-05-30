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

use snarkvm_gadgets::{
    nonnative::{NonNativeFieldMulResultVar, NonNativeFieldVar},
    traits::alloc::AllocGadget,
};
use snarkvm_r1cs::{ConstraintSystem, TestConstraintSystem};
use snarkvm_utilities::rand::UniformRand;

use rand::SeedableRng;
use rand_xorshift::XorShiftRng;

#[test]
fn from_test() {
    type F = snarkvm_curves::bls12_377::Fr;
    type CF = snarkvm_curves::bls12_377::Fq;

    let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

    let mut cs = TestConstraintSystem::<CF>::new();
    let f = F::rand(&mut rng);

    let f_var = NonNativeFieldVar::<F, CF>::alloc_input(&mut cs.ns(|| "alloc_input"), || Ok(f)).unwrap();
    let f_var_converted = NonNativeFieldMulResultVar::<F, CF>::from_nonnative_field_gadget(
        &mut cs.ns(|| "from_nonnative_field_gadget"),
        &f_var,
    )
    .unwrap();
    let f_var_converted_reduced = f_var_converted.reduce(&mut cs.ns(|| "reduce")).unwrap();

    let f_var_value = f_var.value().unwrap();
    let f_var_converted_reduced_value = f_var_converted_reduced.value().unwrap();

    assert_eq!(f_var_value, f_var_converted_reduced_value);
}
