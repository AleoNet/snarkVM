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

use crate::{algorithms::crypto_hash::PoseidonSpongeGadget, AlgebraicSpongeVar, AllocGadget, FieldGadget, FpGadget};
use snarkvm_algorithms::{crypto_hash::PoseidonSponge, AlgebraicSponge};
use snarkvm_curves::bls12_377::Fr;
use snarkvm_fields::PoseidonDefaultField;
use snarkvm_r1cs::{ConstraintSystem, TestConstraintSystem};
use snarkvm_utilities::{test_rng, Uniform};

use std::sync::Arc;

#[test]
fn absorb_test() {
    let mut rng = test_rng();

    let mut cs = TestConstraintSystem::<Fr>::new();

    let absorb: Vec<_> = (0..256).map(|_| Fr::rand(&mut rng)).collect();
    let absorb_var: Vec<_> = absorb
        .iter()
        .enumerate()
        .map(|(i, v)| FpGadget::<Fr>::alloc_input(cs.ns(|| format!("alloc input {}", i)), || Ok(*v)).unwrap())
        .collect();

    let sponge_params = Arc::new(Fr::default_poseidon_parameters::<2>().unwrap());

    let mut native_sponge = PoseidonSponge::new(&sponge_params);
    let mut constraint_sponge = PoseidonSpongeGadget::with_parameters(cs.ns(|| "new sponge"), &sponge_params);

    native_sponge.absorb(&absorb);
    constraint_sponge.absorb(cs.ns(|| "absorb"), absorb_var.iter()).unwrap();

    let native_squeeze = native_sponge.squeeze(1);
    let constraint_squeeze = constraint_sponge.squeeze(cs.ns(|| "squeeze"), 1).unwrap();

    assert_eq!(constraint_squeeze[0].get_value().unwrap(), native_squeeze[0]);
    assert!(cs.is_satisfied());
}
