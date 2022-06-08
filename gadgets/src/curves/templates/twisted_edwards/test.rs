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
    bits::boolean::{AllocatedBit, Boolean},
    curves::tests_group::group_test,
    traits::{alloc::AllocGadget, curves::GroupGadget, select::CondSelectGadget},
};
use snarkvm_curves::{templates::twisted_edwards_extended::Affine as TEAffine, AffineCurve, TwistedEdwardsParameters};
use snarkvm_fields::{Field, PrimeField};
use snarkvm_r1cs::ConstraintSystem;
use snarkvm_utilities::{bititerator::BitIteratorBE, rand::Uniform};

use core::ops::Mul;
use rand::thread_rng;

pub(crate) fn edwards_test<F, P, GG, CS>(cs: &mut CS)
where
    F: Field,
    P: TwistedEdwardsParameters,
    GG: GroupGadget<TEAffine<P>, F, Value = TEAffine<P>>,
    CS: ConstraintSystem<F>,
{
    let a: TEAffine<P> = Uniform::rand(&mut thread_rng());
    let b: TEAffine<P> = Uniform::rand(&mut thread_rng());
    let gadget_a = GG::alloc(&mut cs.ns(|| "a"), || Ok(a)).unwrap();
    let gadget_b = GG::alloc(&mut cs.ns(|| "b"), || Ok(b)).unwrap();
    assert_eq!(gadget_a.get_value().unwrap(), a);
    assert_eq!(gadget_b.get_value().unwrap(), b);
    group_test::<F, TEAffine<P>, GG, _>(&mut cs.ns(|| "GroupTest(a, b)"), gadget_a.clone(), gadget_b);

    // Check mul_bits
    let scalar: <TEAffine<P> as AffineCurve>::ScalarField = Uniform::rand(&mut thread_rng());
    let native_result = a.mul(scalar);

    let mut scalar: Vec<bool> = BitIteratorBE::new(scalar.to_repr()).collect();
    // Get the scalar bits into little-endian form.
    scalar.reverse();
    let input = Vec::<Boolean>::alloc(cs.ns(|| "Input"), || Ok(scalar)).unwrap();
    let zero = GG::zero(cs.ns(|| "zero")).unwrap();
    let result = gadget_a.mul_bits(cs.ns(|| "mul_bits"), &zero, input.into_iter()).unwrap();
    let gadget_value = result.get_value().expect("Gadget_result failed");
    assert_eq!(native_result, gadget_value);
}

pub(crate) fn edwards_constraint_costs<F, P, GG, CS>(cs: &mut CS)
where
    F: Field,
    P: TwistedEdwardsParameters,
    GG: GroupGadget<TEAffine<P>, F, Value = TEAffine<P>>,
    CS: ConstraintSystem<F>,
{
    let bit = AllocatedBit::alloc(&mut cs.ns(|| "bool"), || Ok(true)).unwrap().into();

    let a: TEAffine<P> = rand::random();
    let b: TEAffine<P> = rand::random();
    let gadget_a = GG::alloc(&mut cs.ns(|| "a"), || Ok(a)).unwrap();
    let gadget_b = GG::alloc(&mut cs.ns(|| "b"), || Ok(b)).unwrap();
    let alloc_cost = cs.num_constraints();
    let _ = GG::conditionally_select(&mut cs.ns(|| "cond_select"), &bit, &gadget_a, &gadget_b).unwrap();
    let cond_select_cost = cs.num_constraints() - alloc_cost;

    let _ = gadget_a.add(&mut cs.ns(|| "ab"), &gadget_b).unwrap();
    let add_cost = cs.num_constraints() - cond_select_cost - alloc_cost;
    assert_eq!(cond_select_cost, <GG as CondSelectGadget<_>>::cost());
    assert_eq!(add_cost, GG::cost_of_add());
}
