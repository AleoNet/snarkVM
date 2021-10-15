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
    integers::uint::{Sub, UInt, UInt8},
    traits::{alloc::AllocGadget, bits::Xor, integers::*},
};

fn check_all_constant_bits(mut expected: u8, actual: UInt8) {
    for b in actual.bits.iter() {
        match *b {
            Boolean::Is(_) => panic!(),
            Boolean::Not(_) => panic!(),
            Boolean::Constant(b) => {
                assert!(b == (expected & 1 == 1));
            }
        }

        expected >>= 1;
    }
}

fn check_all_allocated_bits(mut expected: u8, actual: UInt8) {
    for b in actual.bits.iter() {
        match *b {
            Boolean::Is(ref b) => {
                assert!(b.get_value().unwrap() == (expected & 1 == 1));
            }
            Boolean::Not(ref b) => {
                assert!(b.get_value().unwrap() != (expected & 1 == 1));
            }
            Boolean::Constant(_) => unreachable!(),
        }

        expected >>= 1;
    }
}

#[test]
fn test_uint8_from_bits_to_bits() {
    let mut cs = TestConstraintSystem::<Fr>::new();
    let byte_val = 0b01110001;
    let byte = UInt8::alloc(cs.ns(|| "alloc value"), || Ok(byte_val)).unwrap();
    let bits = byte.u8_to_bits_le();
    for (i, bit) in bits.iter().enumerate() {
        assert_eq!(bit.get_value().unwrap(), (byte_val >> i) & 1 == 1)
    }

    assert!(cs.is_satisfied());
}

#[test]
fn test_uint8_alloc_input_vec() {
    let mut cs = TestConstraintSystem::<Fr>::new();
    let byte_vals = (64u8..128u8).collect::<Vec<_>>();
    let bytes = UInt8::alloc_input_vec_le(cs.ns(|| "alloc value"), &byte_vals).unwrap();
    for (native_byte, gadget_byte) in byte_vals.into_iter().zip(bytes) {
        let bits = gadget_byte.u8_to_bits_le();
        for (i, bit) in bits.iter().enumerate() {
            assert_eq!(bit.get_value().unwrap(), (native_byte >> i) & 1 == 1)
        }
    }

    assert!(cs.is_satisfied());
}

#[test]
fn test_uint8_to_bits_be() {
    let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

    for _ in 0..1000 {
        let mut cs = TestConstraintSystem::<Fr>::new();

        let byte_val: u8 = rng.gen();
        let byte = UInt8::alloc(cs.ns(|| "alloc value"), || Ok(byte_val)).unwrap();

        let bits = byte
            .to_bits_be(cs.ns(|| "to_bits_be"))
            .expect("failed to get u8 bits be");
        for (i, bit) in bits.iter().rev().enumerate() {
            assert_eq!(bit.get_value().unwrap(), (byte_val >> i) & 1 == 1);
        }

        assert!(cs.is_satisfied());
    }
}

#[test]
fn test_uint8_to_bits_le() {
    let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

    for _ in 0..1000 {
        let mut cs = TestConstraintSystem::<Fr>::new();

        let byte_val: u8 = rng.gen();
        let byte = UInt8::alloc(cs.ns(|| "alloc value"), || Ok(byte_val)).unwrap();

        let bits = byte
            .to_bits_le(cs.ns(|| "to_bits_le"))
            .expect("failed to get u8 bits be");
        for (i, bit) in bits.iter().enumerate() {
            assert_eq!(bit.get_value().unwrap(), (byte_val >> i) & 1 == 1);
        }

        assert!(cs.is_satisfied());
    }
}

#[test]
fn test_uint8_to_bytes_be() {
    let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

    for _ in 0..1000 {
        let mut cs = TestConstraintSystem::<Fr>::new();

        let byte_val: u8 = rng.gen();
        let bytes = byte_val.to_be_bytes();
        let byte = UInt8::alloc(cs.ns(|| "alloc value"), || Ok(byte_val)).unwrap();

        let bytes_from_gadget = byte
            .to_bytes_be(cs.ns(|| "to_bytes_be"))
            .expect("failed to get u8 bits le")
            .iter()
            .map(|v| v.value.unwrap())
            .collect::<Vec<u8>>();

        assert_eq!(bytes.to_vec(), bytes_from_gadget);
        assert!(cs.is_satisfied());
    }
}

#[test]
fn test_uint8_to_bytes_le() {
    let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

    for _ in 0..1000 {
        let mut cs = TestConstraintSystem::<Fr>::new();

        let byte_val: u8 = rng.gen();
        let bytes = byte_val.to_le_bytes();
        let byte = UInt8::alloc(cs.ns(|| "alloc value"), || Ok(byte_val)).unwrap();

        let bytes_from_gadget = byte
            .to_bytes_le(cs.ns(|| "to_bytes_le"))
            .expect("failed to get u8 bits le")
            .iter()
            .map(|v| v.value.unwrap())
            .collect::<Vec<u8>>();

        assert_eq!(bytes.to_vec(), bytes_from_gadget);
        assert!(cs.is_satisfied());
    }
}

#[test]
fn test_uint8_from_bits_be() {
    let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

    for _ in 0..1000 {
        let mut cs = TestConstraintSystem::<Fr>::new();
        let mut v = (0..8).map(|_| Boolean::constant(rng.gen())).collect::<Vec<_>>();
        v.reverse();

        let b = UInt8::from_bits_be(&v, cs.ns(|| "from_bits_be")).expect("failed to create UInt8 from bits.");

        for (i, bit_gadget) in b.bits.iter().rev().enumerate() {
            match *bit_gadget {
                Boolean::Constant(bit_gadget) => {
                    assert!(bit_gadget == ((b.value.unwrap() >> i) & 1 == 1));
                }
                _ => unreachable!(),
            }
        }

        let expected_to_be_same = b.u8_to_bits_le();

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
fn test_uint8_from_bits_le() {
    let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

    for _ in 0..1000 {
        let mut cs = TestConstraintSystem::<Fr>::new();
        let v = (0..8).map(|_| Boolean::constant(rng.gen())).collect::<Vec<_>>();

        let b = UInt8::from_bits_le(&v, cs.ns(|| "from_bits_le")).expect("failed to create UInt8 from bits.");

        for (i, bit_gadget) in b.bits.iter().enumerate() {
            match *bit_gadget {
                Boolean::Constant(bit_gadget) => {
                    assert!(bit_gadget == ((b.value.unwrap() >> i) & 1 == 1));
                }
                _ => unreachable!(),
            }
        }

        let expected_to_be_same = b.u8_to_bits_le();

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
fn test_uint8_from_bytes_be() {
    let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

    for _ in 0..1000 {
        let expected: u8 = rng.gen();
        let v = expected
            .to_be_bytes()
            .iter()
            .map(|byte| UInt8::constant(*byte))
            .collect::<Vec<UInt8>>();

        let mut cs = TestConstraintSystem::<Fr>::new();

        let b =
            UInt8::from_bytes_be(&v, cs.ns(|| "from_bytes_be_gadget")).expect("failed to create a UInt8 from a byte");

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
fn test_uint8_from_bytes_le() {
    let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

    for _ in 0..1000 {
        let expected: u8 = rng.gen();
        let v = expected
            .to_le_bytes()
            .iter()
            .map(|byte| UInt8::constant(*byte))
            .collect::<Vec<UInt8>>();

        let mut cs = TestConstraintSystem::<Fr>::new();

        let b =
            UInt8::from_bytes_le(&v, cs.ns(|| "from_bytes_le_gadget")).expect("failed to create a UInt8 from a byte");

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
fn test_uint8_to_bits_full() {
    let mut cs = TestConstraintSystem::<Fr>::new();
    let byte_val = 0b01110001;
    let byte = UInt8::alloc(cs.ns(|| "alloc value"), || Ok(byte_val)).unwrap();

    let mut bits_be = byte
        .to_bits_be(cs.ns(|| "to_bits_be"))
        .expect("failed to get u8 bits be");
    let u8_int_from_be =
        UInt8::from_bits_be(&bits_be, cs.ns(|| "from_bits_be")).expect("failed to get u8 from bits be");

    let bits_le = byte
        .to_bits_le(cs.ns(|| "to_bits_le"))
        .expect("failed to get u8 bits le");
    let u8_int_from_le =
        UInt8::from_bits_le(&bits_le, cs.ns(|| "from_bits_le")).expect("failed to get u8 from bits le");

    bits_be.reverse();
    assert_eq!(bits_be, bits_le);
    assert_eq!(byte, u8_int_from_be);
    assert_eq!(byte, u8_int_from_le);
    assert!(cs.is_satisfied());
}

#[test]
fn test_uint8_to_bytes_full() {
    let mut cs = TestConstraintSystem::<Fr>::new();
    let byte_val = 0b01110001;
    let byte = UInt8::alloc(cs.ns(|| "alloc value"), || Ok(byte_val)).unwrap();

    let mut bytes_be = byte
        .to_bytes_be(cs.ns(|| "to_bytes_be"))
        .expect("failed to get u8 bytes be");
    let u8_int_from_be =
        UInt8::from_bytes_be(&bytes_be, cs.ns(|| "from_bytes_be")).expect("failed to get u8 from bytes be");

    let bytes_le = byte
        .to_bytes_le(cs.ns(|| "to_bits_le"))
        .expect("failed to get u8 bytes le");
    let u8_int_from_le =
        UInt8::from_bytes_le(&bytes_le, cs.ns(|| "from_bytes_le")).expect("failed to get u8 from bytes le");

    bytes_be.reverse();
    assert_eq!(bytes_be, bytes_le);
    assert_eq!(byte, u8_int_from_be);
    assert_eq!(byte, u8_int_from_le);
    assert!(cs.is_satisfied());
}

#[test]
fn test_uint8_rotr() {
    let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

    let mut num = rng.gen();

    let a = UInt8::constant(num);

    for i in 0..8 {
        let b = a.rotr(i);

        assert!(b.value.unwrap() == num);

        let mut tmp = num;
        for b in &b.bits {
            match *b {
                Boolean::Constant(b) => {
                    assert_eq!(b, tmp & 1 == 1);
                }
                _ => unreachable!(),
            }

            tmp >>= 1;
        }

        num = num.rotate_right(1);
    }
}

#[test]
fn test_uint8_xor() {
    let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

    for _ in 0..1000 {
        let mut cs = TestConstraintSystem::<Fr>::new();

        let a: u8 = rng.gen();
        let b: u8 = rng.gen();
        let c: u8 = rng.gen();

        let mut expected = a ^ b ^ c;

        let a_bit = UInt8::alloc(cs.ns(|| "a_bit"), || Ok(a)).unwrap();
        let b_bit = UInt8::constant(b);
        let c_bit = UInt8::alloc(cs.ns(|| "c_bit"), || Ok(c)).unwrap();

        let r = a_bit.xor(cs.ns(|| "first xor"), &b_bit).unwrap();
        let r = r.xor(cs.ns(|| "second xor"), &c_bit).unwrap();

        assert!(cs.is_satisfied());

        assert!(r.value == Some(expected));

        for b in r.bits.iter() {
            match *b {
                Boolean::Is(ref b) => {
                    assert!(b.get_value().unwrap() == (expected & 1 == 1));
                }
                Boolean::Not(ref b) => {
                    assert!(b.get_value().unwrap() != (expected & 1 == 1));
                }
                Boolean::Constant(b) => {
                    assert!(b == (expected & 1 == 1));
                }
            }

            expected >>= 1;
        }
    }
}

#[test]
fn test_uint8_addmany_constants() {
    let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

    for _ in 0..1000 {
        let mut cs = TestConstraintSystem::<Fr>::new();

        let a: u8 = rng.gen();
        let b: u8 = rng.gen();
        let c: u8 = rng.gen();

        let a_bit = UInt8::constant(a);
        let b_bit = UInt8::constant(b);
        let c_bit = UInt8::constant(c);

        let expected = a.wrapping_add(b).wrapping_add(c);

        let r = UInt8::addmany(cs.ns(|| "addition"), &[a_bit, b_bit, c_bit]).unwrap();

        assert!(r.value == Some(expected));

        check_all_constant_bits(expected, r);
    }
}

#[test]
#[allow(clippy::many_single_char_names)]
fn test_uint8_addmany() {
    let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

    for _ in 0..1000 {
        let mut cs = TestConstraintSystem::<Fr>::new();

        let a: u8 = rng.gen();
        let b: u8 = rng.gen();
        let c: u8 = rng.gen();
        let d: u8 = rng.gen();

        let expected = (a ^ b).wrapping_add(c).wrapping_add(d);

        let a_bit = UInt8::alloc(cs.ns(|| "a_bit"), || Ok(a)).unwrap();
        let b_bit = UInt8::constant(b);
        let c_bit = UInt8::constant(c);
        let d_bit = UInt8::alloc(cs.ns(|| "d_bit"), || Ok(d)).unwrap();

        let r = a_bit.xor(cs.ns(|| "xor"), &b_bit).unwrap();
        let r = UInt8::addmany(cs.ns(|| "addition"), &[r, c_bit, d_bit]).unwrap();

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
fn test_uint8_sub_constants() {
    let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

    for _ in 0..1000 {
        let mut cs = TestConstraintSystem::<Fr>::new();

        let a: u8 = rng.gen_range(u8::MAX / 2u8..u8::MAX);
        let b: u8 = rng.gen_range(0u8..u8::MAX / 2u8);

        let a_bit = UInt8::constant(a);
        let b_bit = UInt8::constant(b);

        let expected = a.wrapping_sub(b);

        let r = a_bit.sub(cs.ns(|| "subtraction"), &b_bit).unwrap();

        assert!(r.value == Some(expected));

        check_all_constant_bits(expected, r);
    }
}

#[test]
fn test_uint8_sub() {
    let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

    for _ in 0..1000 {
        let mut cs = TestConstraintSystem::<Fr>::new();

        let a: u8 = rng.gen_range(u8::MAX / 2u8..u8::MAX);
        let b: u8 = rng.gen_range(0u8..u8::MAX / 2u8);

        let expected = a.wrapping_sub(b);

        let a_bit = UInt8::alloc(cs.ns(|| "a_bit"), || Ok(a)).unwrap();
        let b_bit = if b > u8::MAX / 4 {
            UInt8::constant(b)
        } else {
            UInt8::alloc(cs.ns(|| "b_bit"), || Ok(b)).unwrap()
        };

        let r = a_bit.sub(cs.ns(|| "subtraction"), &b_bit).unwrap();

        assert!(cs.is_satisfied());

        assert!(r.value == Some(expected));

        check_all_allocated_bits(expected, r);

        // Flip a bit_gadget and see if the subtraction constraint still works
        if cs.get("subtraction/add_not/result bit_gadget 0/boolean").is_zero() {
            cs.set("subtraction/add_not/result bit_gadget 0/boolean", Fr::one());
        } else {
            cs.set("subtraction/add_not/result bit_gadget 0/boolean", Fr::zero());
        }

        assert!(!cs.is_satisfied());
    }
}

#[test]
fn test_uint8_mul_constants() {
    let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

    for _ in 0..1000 {
        let mut cs = TestConstraintSystem::<Fr>::new();

        let a: u8 = rng.gen_range(0..u8::MAX);
        let b: u8 = rng.gen_range(0..u8::MAX);

        let a_bit = UInt8::constant(a);
        let b_bit = UInt8::constant(b);

        let expected = a.wrapping_mul(b);

        let r = a_bit.mul(cs.ns(|| "multiply"), &b_bit).unwrap();

        assert!(r.value == Some(expected));

        check_all_constant_bits(expected, r);
    }
}

#[test]
fn test_uint8_mul() {
    let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

    for _ in 0..1000 {
        let mut cs = TestConstraintSystem::<Fr>::new();

        let a: u8 = rng.gen_range(0..u8::MAX);
        let b: u8 = rng.gen_range(0..u8::MAX);

        let expected = a.wrapping_mul(b);

        let a_bit = UInt8::alloc(cs.ns(|| "a_bit"), || Ok(a)).unwrap();
        let b_bit = if b > u8::MAX / 2 {
            UInt8::constant(b)
        } else {
            UInt8::alloc(cs.ns(|| "b_bit"), || Ok(b)).unwrap()
        };

        let r = a_bit.mul(cs.ns(|| "multiplication"), &b_bit).unwrap();

        assert!(cs.is_satisfied());

        assert!(r.value == Some(expected));

        check_all_allocated_bits(expected, r);

        // Flip a bit_gadget and see if the multiplication constraint still works
        if cs
            .get("multiplication/partial_products/result bit_gadget 0/boolean")
            .is_zero()
        {
            cs.set("multiplication/partial_products/result bit_gadget 0/boolean", Fr::one());
        } else {
            cs.set(
                "multiplication/partial_products/result bit_gadget 0/boolean",
                Fr::zero(),
            );
        }

        assert!(!cs.is_satisfied());
    }
}

#[test]
fn test_uint8_div_constants() {
    let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

    for _ in 0..1000 {
        let mut cs = TestConstraintSystem::<Fr>::new();

        let a: u8 = rng.gen();
        let b: u8 = rng.gen_range(1..u8::MAX);

        let a_bit = UInt8::constant(a);
        let b_bit = UInt8::constant(b);

        let expected = a.wrapping_div(b);

        let r = a_bit.div(cs.ns(|| "division"), &b_bit).unwrap();

        assert!(r.value == Some(expected));

        check_all_constant_bits(expected, r);
    }
}

#[test]
fn test_uint8_div() {
    let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

    for _ in 0..100 {
        let mut cs = TestConstraintSystem::<Fr>::new();

        let a: u8 = rng.gen();
        let b: u8 = rng.gen_range(1..u8::MAX);

        let expected = a.wrapping_div(b);

        let a_bit = UInt8::alloc(cs.ns(|| "a_bit"), || Ok(a)).unwrap();
        let b_bit = if b > u8::MAX / 2 {
            UInt8::constant(b)
        } else {
            UInt8::alloc(cs.ns(|| "b_bit"), || Ok(b)).unwrap()
        };

        let r = a_bit.div(cs.ns(|| "division"), &b_bit).unwrap();

        assert!(cs.is_satisfied());

        assert!(r.value == Some(expected));

        check_all_allocated_bits(expected, r);

        // Flip a bit_gadget and see if the division constraint still works
        if cs
            .get("division/r_sub_d_result_0/allocated bit_gadget 0/boolean")
            .is_zero()
        {
            cs.set("division/r_sub_d_result_0/allocated bit_gadget 0/boolean", Fr::one());
        } else {
            cs.set("division/r_sub_d_result_0/allocated bit_gadget 0/boolean", Fr::zero());
        }

        assert!(!cs.is_satisfied());
    }
}

#[test]
fn test_uint8_pow_constants() {
    let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

    for _ in 0..1000 {
        let mut cs = TestConstraintSystem::<Fr>::new();

        let a: u8 = rng.gen();
        let b: u8 = rng.gen();

        let a_bit = UInt8::constant(a);
        let b_bit = UInt8::constant(b);

        let expected = a.wrapping_pow(b.into());

        let r = a_bit.pow(cs.ns(|| "exponentiation"), &b_bit).unwrap();

        assert!(r.value == Some(expected));

        check_all_constant_bits(expected, r);
    }
}

#[test]
fn test_uint8_pow() {
    let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

    for _ in 0..100 {
        let mut cs = TestConstraintSystem::<Fr>::new();

        let a: u8 = rng.gen();
        let b: u8 = rng.gen();

        let expected = a.wrapping_pow(b.into());

        let a_bit = UInt8::alloc(cs.ns(|| "a_bit"), || Ok(a)).unwrap();
        let b_bit = if b > u8::MAX / 2 {
            UInt8::constant(b)
        } else {
            UInt8::alloc(cs.ns(|| "b_bit"), || Ok(b)).unwrap()
        };

        let r = a_bit.pow(cs.ns(|| "exponentiation"), &b_bit).unwrap();

        assert!(cs.is_satisfied());

        assert!(r.value == Some(expected));

        check_all_allocated_bits(expected, r);

        // Flip a bit_gadget and see if the exponentiation constraint still works
        if cs
            .get("exponentiation/multiply_by_self_0/partial_products/result bit_gadget 0/boolean")
            .is_zero()
        {
            cs.set(
                "exponentiation/multiply_by_self_0/partial_products/result bit_gadget 0/boolean",
                Fr::one(),
            );
        } else {
            cs.set(
                "exponentiation/multiply_by_self_0/partial_products/result bit_gadget 0/boolean",
                Fr::zero(),
            );
        }

        assert!(!cs.is_satisfied());
    }
}
