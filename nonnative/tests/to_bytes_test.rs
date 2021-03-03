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

// use ark_ec::PairingEngine;
// use ark_ff::Zero;
// use ark_mnt4_298::MNT4_298;
// use ark_mnt6_298::MNT6_298;
// use ark_nonnative_field::NonNativeFieldVar;
// use ark_r1cs_std::alloc::AllocVar;
// use ark_r1cs_std::{R1CSVar, ToBitsGadget, ToBytesGadget};
// use ark_relations::r1cs::ConstraintSystem;

use snarkvm_fields::Zero;
use snarkvm_gadgets::traits::utilities::{alloc::AllocGadget, ToBitsGadget, ToBytesGadget};
use snarkvm_nonnative::NonNativeFieldVar;
use snarkvm_r1cs::{ConstraintSystem, TestConstraintSystem};

// #[test]
// fn to_bytes_test() {
//     let cs = ConstraintSystem::<<MNT6_298 as PairingEngine>::Fr>::new_ref();
//
//     let target_test_elem = <MNT4_298 as PairingEngine>::Fr::from(123456u128);
//     let target_test_gadget = NonNativeFieldVar::<
//         <MNT4_298 as PairingEngine>::Fr,
//         <MNT6_298 as PairingEngine>::Fr,
//     >::new_witness(cs, || Ok(target_test_elem))
//     .unwrap();
//
//     let target_to_bytes: Vec<u8> = target_test_gadget
//         .to_bytes()
//         .unwrap()
//         .iter()
//         .map(|v| v.value().unwrap())
//         .collect();
//
//     // 123456 = 65536 + 226 * 256 + 64
//     assert_eq!(target_to_bytes[0], 64);
//     assert_eq!(target_to_bytes[1], 226);
//     assert_eq!(target_to_bytes[2], 1);
//
//     for byte in target_to_bytes.iter().skip(3) {
//         assert_eq!(*byte, 0);
//     }
// }

#[test]
fn to_bits_test() {
    type F = snarkvm_curves::bls12_377::Fr;
    type CF = snarkvm_curves::bls12_377::Fq;

    let mut cs = TestConstraintSystem::<CF>::new();
    let f = F::zero();

    let f_var = NonNativeFieldVar::<F, CF>::alloc_input(&mut cs.ns(|| "alloc_input_nonnative"), || Ok(f)).unwrap();
    f_var.to_bits(cs).unwrap();
}
