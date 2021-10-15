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

use rand::{Rng, SeedableRng};
use rand_xorshift::XorShiftRng;

use snarkvm_fields::{One, Zero};
use snarkvm_r1cs::{ConstraintSystem, Fr, TestConstraintSystem};

use crate::{
    bits::{
        Boolean,
        FromBitsBEGadget,
        FromBitsLEGadget,
        FromBytesBEGadget,
        FromBytesLEGadget,
        ToBitsBEGadget,
        ToBitsLEGadget,
        ToBytesBEGadget,
        ToBytesLEGadget,
    },
    integers::int::*,
    traits::{alloc::AllocGadget, eq::EqGadget, integers::*},
    UInt8,
};

fn check_all_constant_bits(expected: i64, actual: Int64) {
    for (i, b) in actual.bits.iter().enumerate() {
        // shift value by i
        let mask = 1 << i as i64;
        let result = expected & mask;

        match *b {
            Boolean::Is(_) => panic!(),
            Boolean::Not(_) => panic!(),
            Boolean::Constant(b) => {
                let bit = result == mask;
                assert_eq!(b, bit);
            }
        }
    }
}

fn check_all_allocated_bits(expected: i64, actual: Int64) {
    for (i, b) in actual.bits.iter().enumerate() {
        // shift value by i
        let mask = 1 << i as i64;
        let result = expected & mask;

        match *b {
            Boolean::Is(ref b) => {
                let bit = result == mask;
                assert_eq!(b.get_value().unwrap(), bit);
            }
            Boolean::Not(ref b) => {
                let bit = result == mask;
                assert_eq!(!b.get_value().unwrap(), bit);
            }
            Boolean::Constant(_) => unreachable!(),
        }
    }
}

#[test]
fn test_int64_constant_and_alloc() {
    let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

    for _ in 0..1000 {
        let mut cs = TestConstraintSystem::<Fr>::new();

        let a: i64 = rng.gen();

        let a_const = Int64::constant(a);

        assert!(a_const.value == Some(a));

        let a_bit = Int64::alloc(cs.ns(|| "a_bit"), || Ok(a)).unwrap();

        assert!(cs.is_satisfied());
        assert!(a_bit.value == Some(a));

        let a_bit_fe = Int64::alloc_input_fe(cs.ns(|| "a_bit_fe"), a).unwrap();

        a_bit_fe.enforce_equal(cs.ns(|| "a_bit_fe == a_bit"), &a_bit).unwrap();

        assert!(cs.is_satisfied());
        assert!(a_bit_fe.value == Some(a));

        check_all_constant_bits(a, a_const);
        check_all_allocated_bits(a, a_bit);
        check_all_allocated_bits(a, a_bit_fe);
    }
}

#[test]
fn test_int64_to_bits_be() {
    let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

    for _ in 0..1000 {
        let mut cs = TestConstraintSystem::<Fr>::new();

        let byte_val: i64 = rng.gen();
        let byte = Int64::alloc(cs.ns(|| "alloc value"), || Ok(byte_val)).unwrap();

        let bits = byte
            .to_bits_be(cs.ns(|| "to_bits_be"))
            .expect("failed to get i64 bits be");
        for (i, bit) in bits.iter().rev().enumerate() {
            assert_eq!(bit.get_value().unwrap(), (byte_val >> i) & 1 == 1);
        }

        assert!(cs.is_satisfied());
    }
}

#[test]
fn test_int64_to_bits_le() {
    let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

    for _ in 0..1000 {
        let mut cs = TestConstraintSystem::<Fr>::new();

        let byte_val: i64 = rng.gen();
        let byte = Int64::alloc(cs.ns(|| "alloc value"), || Ok(byte_val)).unwrap();

        let bits = byte
            .to_bits_le(cs.ns(|| "to_bits_le"))
            .expect("failed to get i64 bits be");
        for (i, bit) in bits.iter().enumerate() {
            assert_eq!(bit.get_value().unwrap(), (byte_val >> i) & 1 == 1);
        }

        assert!(cs.is_satisfied());
    }
}

#[test]
fn test_int64_to_bytes_be() {
    let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

    for _ in 0..1000 {
        let mut cs = TestConstraintSystem::<Fr>::new();

        let byte_val: i64 = rng.gen();
        let bytes = byte_val.to_be_bytes();
        let byte = Int64::alloc(cs.ns(|| "alloc value"), || Ok(byte_val)).unwrap();

        let bytes_from_gadget = byte
            .to_bytes_be(cs.ns(|| "to_bytes_be"))
            .expect("failed to get i64 bits le")
            .iter()
            .map(|v| v.value.unwrap())
            .collect::<Vec<u8>>();

        assert_eq!(bytes.to_vec(), bytes_from_gadget);
        assert!(cs.is_satisfied());
    }
}

#[test]
fn test_int64_to_bytes_le() {
    let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

    for _ in 0..1000 {
        let mut cs = TestConstraintSystem::<Fr>::new();

        let byte_val: i64 = rng.gen();
        let bytes = byte_val.to_le_bytes();
        let byte = Int64::alloc(cs.ns(|| "alloc value"), || Ok(byte_val)).unwrap();

        let bytes_from_gadget = byte
            .to_bytes_le(cs.ns(|| "to_bytes_le"))
            .expect("failed to get i64 bits le")
            .iter()
            .map(|v| v.value.unwrap())
            .collect::<Vec<u8>>();

        assert_eq!(bytes.to_vec(), bytes_from_gadget);
        assert!(cs.is_satisfied());
    }
}

#[test]
fn test_int64_from_bits_be() {
    let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

    for _ in 0..1000 {
        let mut cs = TestConstraintSystem::<Fr>::new();
        let mut v = (0..64).map(|_| Boolean::constant(rng.gen())).collect::<Vec<_>>();
        v.reverse();

        let b = Int64::from_bits_be(&v, cs.ns(|| "from_bits_be")).expect("failed to create Int64 from bits.");

        for (i, bit_gadget) in b.bits.iter().rev().enumerate() {
            match *bit_gadget {
                Boolean::Constant(bit_gadget) => {
                    assert!(bit_gadget == ((b.value.unwrap() >> i) & 1 == 1));
                }
                _ => unreachable!(),
            }
        }

        let expected_to_be_same = b.bits.clone();

        for x in v.iter().zip(expected_to_be_same.iter()) {
            match x {
                (&Boolean::Constant(true), &Boolean::Constant(true)) => {}
                (&Boolean::Constant(false), &Boolean::Constant(false)) => {}
                _ => unreachable!(),
            }
        }

        assert!(cs.is_satisfied());
    }
}

#[test]
fn test_int64_from_bits_le() {
    let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

    for _ in 0..1000 {
        let mut cs = TestConstraintSystem::<Fr>::new();
        let v = (0..64).map(|_| Boolean::constant(rng.gen())).collect::<Vec<_>>();

        let b = Int64::from_bits_le(&v, cs.ns(|| "from_bits_le")).expect("failed to create Int64 from bits.");

        for (i, bit_gadget) in b.bits.iter().enumerate() {
            match *bit_gadget {
                Boolean::Constant(bit_gadget) => {
                    assert!(bit_gadget == ((b.value.unwrap() >> i) & 1 == 1));
                }
                _ => unreachable!(),
            }
        }

        let expected_to_be_same = b.bits.clone();

        for x in v.iter().zip(expected_to_be_same.iter()) {
            match x {
                (&Boolean::Constant(true), &Boolean::Constant(true)) => {}
                (&Boolean::Constant(false), &Boolean::Constant(false)) => {}
                _ => unreachable!(),
            }
        }

        assert!(cs.is_satisfied());
    }
}

#[test]
fn test_int64_from_bytes_be() {
    let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

    for _ in 0..1000 {
        let expected: i64 = rng.gen();
        let v = expected
            .to_be_bytes()
            .iter()
            .map(|byte| UInt8::constant(*byte))
            .collect::<Vec<UInt8>>();

        let mut cs = TestConstraintSystem::<Fr>::new();

        let b =
            Int64::from_bytes_be(&v, cs.ns(|| "from_bytes_be_gadget")).expect("failed to create a Int64 from a byte");

        // check bits
        for (i, bit_gadget) in b.bits.iter().enumerate() {
            match *bit_gadget {
                Boolean::Constant(bit_gadget) => {
                    assert!(bit_gadget == ((b.value.unwrap() >> i) & 1 == 1));
                }
                _ => unreachable!(),
            }
        }

        assert!(cs.is_satisfied());
    }
}

#[test]
fn test_int64_from_bytes_le() {
    let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

    for _ in 0..1000 {
        let expected: i64 = rng.gen();
        let v = expected
            .to_le_bytes()
            .iter()
            .map(|byte| UInt8::constant(*byte))
            .collect::<Vec<UInt8>>();

        let mut cs = TestConstraintSystem::<Fr>::new();

        let b =
            Int64::from_bytes_le(&v, cs.ns(|| "from_bytes_le_gadget")).expect("failed to create a Int64 from a byte");

        // check bits
        for (i, bit_gadget) in b.bits.iter().enumerate() {
            match *bit_gadget {
                Boolean::Constant(bit_gadget) => {
                    assert!(bit_gadget == ((b.value.unwrap() >> i) & 1 == 1));
                }
                _ => unreachable!(),
            }
        }

        assert!(cs.is_satisfied());
    }
}

#[test]
fn test_int64_to_bits_full() {
    let mut cs = TestConstraintSystem::<Fr>::new();
    let byte_val = 0b01110001;
    let byte = Int64::alloc(cs.ns(|| "alloc value"), || Ok(byte_val)).unwrap();

    let mut bits_be = byte
        .to_bits_be(cs.ns(|| "to_bits_be"))
        .expect("failed to get i64 bits be");
    let i64_int_from_be =
        Int64::from_bits_be(&bits_be, cs.ns(|| "from_bits_be")).expect("failed to get i64 from bits be");

    let bits_le = byte
        .to_bits_le(cs.ns(|| "to_bits_le"))
        .expect("failed to get i64 bits le");
    let i64_int_from_le =
        Int64::from_bits_le(&bits_le, cs.ns(|| "from_bits_le")).expect("failed to get i64 from bits le");

    bits_be.reverse();
    assert_eq!(bits_be, bits_le);
    assert_eq!(byte, i64_int_from_be);
    assert_eq!(byte, i64_int_from_le);
    assert!(cs.is_satisfied());
}

#[test]
fn test_int64_to_bytes_full() {
    let mut cs = TestConstraintSystem::<Fr>::new();
    let byte_val = 0b01110001;
    let byte = Int64::alloc(cs.ns(|| "alloc value"), || Ok(byte_val)).unwrap();

    let mut bytes_be = byte
        .to_bytes_be(cs.ns(|| "to_bytes_be"))
        .expect("failed to get i64 bytes be");
    let i64_int_from_be =
        Int64::from_bytes_be(&bytes_be, cs.ns(|| "from_bytes_be")).expect("failed to get i64 from bytes be");

    let bytes_le = byte
        .to_bytes_le(cs.ns(|| "to_bits_le"))
        .expect("failed to get i64 bytes le");
    let i64_int_from_le =
        Int64::from_bytes_le(&bytes_le, cs.ns(|| "from_bytes_le")).expect("failed to get i64 from bytes le");

    bytes_be.reverse();
    assert_eq!(bytes_be, bytes_le);
    assert_eq!(byte, i64_int_from_be);
    assert_eq!(byte, i64_int_from_le);
    assert!(cs.is_satisfied());
}

#[test]
fn test_int64_add_constants() {
    let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

    for _ in 0..1000 {
        let mut cs = TestConstraintSystem::<Fr>::new();

        let a: i64 = rng.gen();
        let b: i64 = rng.gen();

        let a_bit = Int64::constant(a);
        let b_bit = Int64::constant(b);

        let expected = match a.checked_add(b) {
            Some(valid) => valid,
            None => continue,
        };

        let r = a_bit.add(cs.ns(|| "addition"), &b_bit).unwrap();

        assert!(r.value == Some(expected));

        check_all_constant_bits(expected, r);
    }
}

#[test]
fn test_int64_add() {
    let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

    for _ in 0..1000 {
        let mut cs = TestConstraintSystem::<Fr>::new();

        let a: i64 = rng.gen();
        let b: i64 = rng.gen();

        let expected = match a.checked_add(b) {
            Some(valid) => valid,
            None => continue,
        };

        let a_bit = Int64::alloc(cs.ns(|| "a_bit"), || Ok(a)).unwrap();
        let b_bit = Int64::alloc(cs.ns(|| "b_bit"), || Ok(b)).unwrap();

        let r = a_bit.add(cs.ns(|| "addition"), &b_bit).unwrap();

        assert!(cs.is_satisfied());

        assert!(r.value == Some(expected));

        check_all_allocated_bits(expected, r);

        // Flip a bit_gadget and see if the addition constraint still works
        if cs.get("addition/result bit_gadget 0/boolean").is_zero() {
            cs.set("addition/result bit_gadget 0/boolean", Fr::one());
        } else {
            cs.set("addition/result bit_gadget 0/boolean", Fr::zero());
        }

        assert!(!cs.is_satisfied());
    }
}

#[test]
fn test_int64_sub_constants() {
    let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

    for _ in 0..1000 {
        let mut cs = TestConstraintSystem::<Fr>::new();

        let a: i64 = rng.gen();
        let b: i64 = rng.gen();

        if b.checked_neg().is_none() {
            // negate with overflows will fail: -128
            continue;
        }
        let expected = match a.checked_sub(b) {
            // subtract with overflow will fail: -0
            Some(valid) => valid,
            None => continue,
        };

        let a_bit = Int64::constant(a);
        let b_bit = Int64::constant(b);

        let r = a_bit.sub(cs.ns(|| "subtraction"), &b_bit).unwrap();

        assert!(r.value == Some(expected));

        check_all_constant_bits(expected, r);
    }
}

#[test]
fn test_int64_sub() {
    let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

    for _ in 0..1000 {
        let mut cs = TestConstraintSystem::<Fr>::new();

        let a: i64 = rng.gen();
        let b: i64 = rng.gen();

        if b.checked_neg().is_none() {
            // negate with overflows will fail: -9223372036854775808
            continue;
        }
        let expected = match a.checked_sub(b) {
            // subtract with overflow will fail: -0
            Some(valid) => valid,
            None => continue,
        };

        let a_bit = Int64::alloc(cs.ns(|| "a_bit"), || Ok(a)).unwrap();
        let b_bit = Int64::alloc(cs.ns(|| "b_bit"), || Ok(b)).unwrap();

        let r = a_bit.sub(cs.ns(|| "subtraction"), &b_bit).unwrap();

        assert!(cs.is_satisfied());

        assert!(r.value == Some(expected));

        check_all_allocated_bits(expected, r);

        // Flip a bit_gadget and see if the subtraction constraint still works
        if cs
            .get("subtraction/add_complement/result bit_gadget 0/boolean")
            .is_zero()
        {
            cs.set("subtraction/add_complement/result bit_gadget 0/boolean", Fr::one());
        } else {
            cs.set("subtraction/add_complement/result bit_gadget 0/boolean", Fr::zero());
        }

        assert!(!cs.is_satisfied());
    }
}

#[test]
fn test_int64_mul_constants() {
    let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

    for _ in 0..5 {
        let mut cs = TestConstraintSystem::<Fr>::new();

        let max = i32::MAX as i64;
        let min = i32::MIN as i64;

        let a: i64 = rng.gen_range(min..max);
        let b: i64 = rng.gen_range(min..max);

        let expected = match a.checked_mul(b) {
            Some(valid) => valid,
            None => continue,
        };

        let a_bit = Int64::constant(a);
        let b_bit = Int64::constant(b);

        let r = a_bit.mul(cs.ns(|| "multiplication"), &b_bit).unwrap();

        assert!(r.value == Some(expected));

        check_all_constant_bits(expected, r);
    }
}

#[test]
fn test_int64_mul() {
    let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

    for _ in 0..5 {
        let mut cs = TestConstraintSystem::<Fr>::new();

        let max = i32::MAX as i64;
        let min = i32::MIN as i64;

        let a: i64 = rng.gen_range(min..max);
        let b: i64 = rng.gen_range(min..max);

        let expected = match a.checked_mul(b) {
            Some(valid) => valid,
            None => continue,
        };

        let a_bit = Int64::alloc(cs.ns(|| "a_bit"), || Ok(a)).unwrap();
        let b_bit = Int64::alloc(cs.ns(|| "b_bit"), || Ok(b)).unwrap();

        let r = a_bit.mul(cs.ns(|| "multiplication"), &b_bit).unwrap();

        assert!(cs.is_satisfied());

        assert!(r.value == Some(expected));

        check_all_allocated_bits(expected, r);

        // Flip a bit_gadget and see if the multiplication constraint still works
        if cs.get("multiplication/result bit_gadget 0/boolean").is_zero() {
            cs.set("multiplication/result bit_gadget 0/boolean", Fr::one());
        } else {
            cs.set("multiplication/result bit_gadget 0/boolean", Fr::zero());
        }

        assert!(!cs.is_satisfied());
    }
}

#[test]
fn test_int64_div_constants() {
    let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

    for _ in 0..3 {
        let mut cs = TestConstraintSystem::<Fr>::new();

        let a: i64 = rng.gen();
        let b: i64 = rng.gen();

        if a.checked_neg().is_none() {
            return;
        }

        let expected = match a.checked_div(b) {
            Some(valid) => valid,
            None => return,
        };

        let a_bit = Int64::constant(a);
        let b_bit = Int64::constant(b);

        let r = a_bit.div(cs.ns(|| "division"), &b_bit).unwrap();

        assert!(r.value == Some(expected));

        check_all_constant_bits(expected, r);
    }
}

#[test]
fn test_int64_div() {
    let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

    for _ in 0..3 {
        let mut cs = TestConstraintSystem::<Fr>::new();

        let a: i64 = rng.gen();
        let b: i64 = rng.gen();

        if a.checked_neg().is_none() {
            continue;
        }

        let expected = match a.checked_div(b) {
            Some(valid) => valid,
            None => return,
        };

        let a_bit = Int64::alloc(cs.ns(|| "a_bit"), || Ok(a)).unwrap();
        let b_bit = Int64::alloc(cs.ns(|| "b_bit"), || Ok(b)).unwrap();

        let r = a_bit.div(cs.ns(|| "division"), &b_bit).unwrap();

        assert!(cs.is_satisfied());

        assert!(r.value == Some(expected));

        check_all_allocated_bits(expected, r);
    }
}

#[test]
fn test_int64_pow_constants() {
    let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

    for _ in 0..5 {
        let mut cs = TestConstraintSystem::<Fr>::new();

        let a: i64 = rng.gen_range(-3037000499..3037000499);
        let b: i64 = rng.gen_range(-3..3);

        let expected = match a.checked_pow(b as u32) {
            Some(valid) => valid,
            None => continue,
        };

        let a_bit = Int64::constant(a);
        let b_bit = Int64::constant(b);

        let r = a_bit.pow(cs.ns(|| "exponentiation"), &b_bit).unwrap();

        assert!(r.value == Some(expected));

        check_all_constant_bits(expected, r);
    }
}

#[test]
fn test_int64_pow() {
    let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

    for _ in 0..5 {
        let mut cs = TestConstraintSystem::<Fr>::new();

        let a: i64 = rng.gen_range(-3037000499..3037000499);
        let b: i64 = rng.gen_range(-3..3);

        let expected = match a.checked_pow(b as u32) {
            Some(valid) => valid,
            None => continue,
        };

        let a_bit = Int64::alloc(cs.ns(|| "a_bit"), || Ok(a)).unwrap();
        let b_bit = Int64::alloc(cs.ns(|| "b_bit"), || Ok(b)).unwrap();

        let r = a_bit.pow(cs.ns(|| "exponentiation"), &b_bit).unwrap();

        assert!(cs.is_satisfied());

        assert!(r.value == Some(expected));

        check_all_allocated_bits(expected, r);

        // Flip a bit_gadget and see if the exponentiation constraint still works
        if cs
            .get("exponentiation/multiply_by_self_0/result bit_gadget 0/boolean")
            .is_zero()
        {
            cs.set(
                "exponentiation/multiply_by_self_0/result bit_gadget 0/boolean",
                Fr::one(),
            );
        } else {
            cs.set(
                "exponentiation/multiply_by_self_0/result bit_gadget 0/boolean",
                Fr::zero(),
            );
        }

        assert!(!cs.is_satisfied());
    }
}
