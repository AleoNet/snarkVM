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

use snarkvm_curves::{bls12_377::Bls12_377, bw6_761::BW6_761, pairing_engine::PairingEngine};
use snarkvm_fields::Zero;
use snarkvm_gadgets::{
    bits::{ToBitsBEGadget, ToBitsLEGadget, ToBytesLEGadget},
    nonnative::NonNativeFieldVar,
    traits::alloc::AllocGadget,
};
use snarkvm_r1cs::{ConstraintSystem, TestConstraintSystem};

#[test]
fn to_bytes_test() {
    let mut cs = TestConstraintSystem::<<BW6_761 as PairingEngine>::Fr>::new();

    let target_test_gadget =
        NonNativeFieldVar::<<Bls12_377 as PairingEngine>::Fr, <BW6_761 as PairingEngine>::Fr>::alloc(
            cs.ns(|| "alloc"),
            || Ok(<Bls12_377 as PairingEngine>::Fr::from(123456u128)),
        )
        .unwrap();

    let target_to_bytes: Vec<u8> = target_test_gadget
        .to_bytes_le(cs)
        .unwrap()
        .iter()
        .map(|v| v.value.unwrap())
        .collect();

    // 123456 = 65536 + 226 * 256 + 64
    assert_eq!(target_to_bytes[0], 64);
    assert_eq!(target_to_bytes[1], 226);
    assert_eq!(target_to_bytes[2], 1);

    for byte in target_to_bytes.iter().skip(3) {
        assert_eq!(*byte, 0);
    }
}

#[test]
fn to_bits_le_test() {
    type F = snarkvm_curves::bls12_377::Fr;
    type CF = snarkvm_curves::bls12_377::Fq;

    let mut cs = TestConstraintSystem::<CF>::new();
    let f = F::zero();

    let f_var = NonNativeFieldVar::<F, CF>::alloc_input(&mut cs.ns(|| "alloc_input_nonnative"), || Ok(f)).unwrap();
    f_var.to_bits_le(cs).unwrap();
}

#[test]
fn to_bits_be_test() {
    type F = snarkvm_curves::bls12_377::Fr;
    type CF = snarkvm_curves::bls12_377::Fq;

    let mut cs = TestConstraintSystem::<CF>::new();
    let f = F::zero();

    let f_var = NonNativeFieldVar::<F, CF>::alloc_input(&mut cs.ns(|| "alloc_input_nonnative"), || Ok(f)).unwrap();
    f_var.to_bits_be(cs).unwrap();
}
