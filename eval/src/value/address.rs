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

use crate::{errors::AddressError, ConstrainedValue, GroupType};

use snarkvm_dpc::{account::address, testnet1::instantiated::Components};
use snarkvm_fields::{Field, PrimeField};
use snarkvm_gadgets::{
    boolean::Boolean,
    integers::uint::UInt8,
    traits::{
        alloc::AllocGadget,
        eq::{ConditionalEqGadget, EqGadget, EvaluateEqGadget},
        select::CondSelectGadget,
    },
    FromBitsBEGadget,
    FromBitsLEGadget,
    FromBytesBEGadget,
    FromBytesLEGadget,
    Integer,
    ToBitsBEGadget,
    ToBitsLEGadget,
    ToBytesBEGadget,
    ToBytesLEGadget,
};
use snarkvm_ir::Value;
use snarkvm_r1cs::{Assignment, ConstraintSystem, SynthesisError};
use snarkvm_utilities::{FromBytes, ToBytes};
use std::{borrow::Borrow, str::FromStr};

/// A public address
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Address {
    pub address: address::Address<Components>,
    pub bytes: Vec<UInt8>,
}

impl Address {
    pub(crate) fn constant(address_bytes: &[u8]) -> Result<Self, AddressError> {
        let mut address_bytes_reader = address_bytes;
        let address = address::Address::read_le(&mut address_bytes_reader)
            .map_err(|error| AddressError::account_error(error.into()))?;

        let bytes = UInt8::constant_vec(address_bytes);

        Ok(Address { address, bytes })
    }

    pub(crate) fn is_constant(&self) -> bool {
        self.bytes.iter().all(|byte| byte.is_constant())
    }

    pub(crate) fn from_input<F: PrimeField, G: GroupType<F>, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        name: &str,
        value: Value,
    ) -> Result<ConstrainedValue<F, G>, AddressError> {
        // Check that the input value is the correct type
        let value = if let Value::Address(value) = value {
            value
        } else {
            return Err(AddressError::invalid_address(name));
        };

        let account =
            address::Address::read_le(&mut &value[..]).map_err(|error| AddressError::account_error(error.into()))?;
        let bytes = UInt8::alloc_vec(cs, &value[..])?;

        let address = Address {
            address: account,
            bytes,
        };

        Ok(ConstrainedValue::Address(address))
    }

    pub(crate) fn alloc_helper<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<String>>(
        value_gen: Fn,
    ) -> Result<address::Address<Components>, SynthesisError> {
        let address_string = match value_gen() {
            Ok(value) => {
                let string_value = value.borrow().clone();
                Ok(string_value)
            }
            _ => Err(SynthesisError::AssignmentMissing),
        }?;

        address::Address::from_str(&address_string).map_err(|_| SynthesisError::AssignmentMissing)
    }
}

impl<F: PrimeField> AllocGadget<String, F> for Address {
    fn alloc<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<String>, CS: ConstraintSystem<F>>(
        cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let address = Self::alloc_helper(value_gen)?;
        let mut address_bytes = vec![];
        address
            .write_le(&mut address_bytes)
            .map_err(|_| SynthesisError::AssignmentMissing)?;

        let bytes = UInt8::alloc_vec(cs, &address_bytes[..])?;

        Ok(Address { address, bytes })
    }

    fn alloc_input<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<String>, CS: ConstraintSystem<F>>(
        cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let address = Self::alloc_helper(value_gen)?;
        let mut address_bytes = vec![];
        address
            .write_le(&mut address_bytes)
            .map_err(|_| SynthesisError::AssignmentMissing)?;

        let bytes = UInt8::alloc_input_vec_le(cs, &address_bytes[..])?;

        Ok(Address { address, bytes })
    }
}

impl<F: PrimeField> EvaluateEqGadget<F> for Address {
    fn evaluate_equal<CS: ConstraintSystem<F>>(&self, mut cs: CS, other: &Self) -> Result<Boolean, SynthesisError> {
        if self.bytes.len() != other.bytes.len() {
            return Err(SynthesisError::Unsatisfiable);
        }

        if self.is_constant() && other.is_constant() {
            Ok(Boolean::Constant(self.eq(other)))
        } else {
            let mut result = Boolean::constant(true);

            for (i, (a, b)) in self.bytes.iter().zip(&other.bytes).enumerate() {
                let equal =
                    a.evaluate_equal(&mut cs.ns(|| format!("address evaluate equality for {}-th byte", i)), b)?;

                result = Boolean::and(
                    &mut cs.ns(|| format!("address and result for {}-th byte", i)),
                    &equal,
                    &result,
                )?;
            }

            Ok(result)
        }
    }
}

fn cond_equal_helper(first: &Address, second: &Address, cond: bool) -> Result<(), SynthesisError> {
    if cond {
        if first.eq(second) {
            Ok(())
        } else {
            Err(SynthesisError::Unsatisfiable)
        }
    } else {
        Ok(())
    }
}

impl<F: PrimeField> ConditionalEqGadget<F> for Address {
    fn conditional_enforce_equal<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        other: &Self,
        condition: &Boolean,
    ) -> Result<(), SynthesisError> {
        if let Boolean::Constant(cond) = *condition {
            cond_equal_helper(self, other, cond)
        } else {
            if self.bytes.len() != other.bytes.len() {
                return Err(SynthesisError::Unsatisfiable);
            }

            for (i, (a, b)) in self.bytes.iter().zip(&other.bytes).enumerate() {
                a.conditional_enforce_equal(
                    &mut cs.ns(|| format!("address equality check for {}-th byte", i)),
                    b,
                    condition,
                )?;
            }
            Ok(())
        }
    }

    fn cost() -> usize {
        <UInt8 as ConditionalEqGadget<F>>::cost() * 32 // address 32 bytes
    }
}

fn cond_select_helper(first: &Address, second: &Address, cond: bool) -> Address {
    if cond { first.clone() } else { second.clone() }
}

impl<F: PrimeField> CondSelectGadget<F> for Address {
    fn conditionally_select<CS: ConstraintSystem<F>>(
        mut cs: CS,
        cond: &Boolean,
        first: &Self,
        second: &Self,
    ) -> Result<Self, SynthesisError> {
        if let Boolean::Constant(cond) = *cond {
            Ok(cond_select_helper(first, second, cond))
        } else {
            let result_val = cond.get_value().and_then(|c| {
                if c {
                    Some(first.address.clone())
                } else {
                    Some(second.address.clone())
                }
            });

            let result = Self::alloc(cs.ns(|| "cond_select_result"), || {
                result_val.get().map(|v| v.to_string())
            })?;

            if first.bytes.len() != second.bytes.len() {
                return Err(SynthesisError::Unsatisfiable);
            }

            let expected_bytes = first
                .bytes
                .iter()
                .zip(&second.bytes)
                .enumerate()
                .map(|(i, (a, b))| {
                    UInt8::conditionally_select(&mut cs.ns(|| format!("address_cond_select_{}", i)), cond, a, b)
                        .unwrap()
                })
                .collect::<Vec<UInt8>>();

            for (i, (actual, expected)) in result.bytes.iter().zip(expected_bytes.iter()).enumerate() {
                actual.enforce_equal(&mut cs.ns(|| format!("selected_result_byte_{}", i)), expected)?;
            }

            Ok(result)
        }
    }

    fn cost() -> usize {
        <UInt8 as CondSelectGadget<F>>::cost() * 32
    }
}

impl<F: PrimeField> ToBitsLEGadget<F> for Address {
    fn to_bits_le<CS: ConstraintSystem<F>>(&self, mut cs: CS) -> Result<Vec<Boolean>, SynthesisError> {
        Ok(self
            .bytes
            .iter()
            .enumerate()
            .map(|(i, byte)| byte.to_bits_le(cs.ns(|| format!("to_bits_le_{}", i))))
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .flatten()
            .collect())
    }

    fn to_bits_le_strict<CS: ConstraintSystem<F>>(&self, mut cs: CS) -> Result<Vec<Boolean>, SynthesisError> {
        Ok(self
            .bytes
            .iter()
            .enumerate()
            .map(|(i, byte)| byte.to_bits_le_strict(cs.ns(|| format!("to_bits_le_{}", i))))
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .flatten()
            .collect())
    }
}

impl<F: PrimeField> ToBitsBEGadget<F> for Address {
    fn to_bits_be<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<Boolean>, SynthesisError> {
        let mut bits = self.to_bits_le(cs)?;
        bits.reverse();
        Ok(bits)
    }

    fn to_bits_be_strict<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<Boolean>, SynthesisError> {
        let mut bits = self.to_bits_le_strict(cs)?;
        bits.reverse();
        Ok(bits)
    }
}

impl<F: Field> FromBitsBEGadget<F> for Address {
    fn from_bits_be<CS: ConstraintSystem<F>>(bits: &[Boolean], _cs: CS) -> Result<Address, SynthesisError> {
        if bits.len() != 256 {
            return Err(SynthesisError::AssignmentMissing);
        }

        let mut bits = bits.to_vec();
        bits.reverse();

        let bytes = bits
            .chunks(8)
            .into_iter()
            .map(|chunk8| UInt8::u8_from_bits_le(chunk8).map(|v| v.value.ok_or(SynthesisError::Unsatisfiable)))
            .flatten()
            .collect::<Result<Vec<u8>, SynthesisError>>()?;

        Self::constant(&bytes).map_err(|_| SynthesisError::Unsatisfiable)
    }

    fn from_bits_be_strict<CS: ConstraintSystem<F>>(bits: &[Boolean], cs: CS) -> Result<Address, SynthesisError> {
        <Self as FromBitsBEGadget<F>>::from_bits_be(bits, cs)
    }
}

impl<F: Field> FromBitsLEGadget<F> for Address {
    fn from_bits_le<CS: ConstraintSystem<F>>(bits: &[Boolean], _cs: CS) -> Result<Address, SynthesisError> {
        if bits.len() != 256 {
            return Err(SynthesisError::AssignmentMissing);
        }

        let bytes = bits
            .chunks(8)
            .into_iter()
            .map(|chunk8| UInt8::u8_from_bits_le(chunk8).map(|v| v.value.ok_or(SynthesisError::Unsatisfiable)))
            .flatten()
            .collect::<Result<Vec<u8>, SynthesisError>>()?;

        Self::constant(&bytes).map_err(|_| SynthesisError::Unsatisfiable)
    }

    fn from_bits_le_strict<CS: ConstraintSystem<F>>(bits: &[Boolean], cs: CS) -> Result<Address, SynthesisError> {
        <Self as FromBitsLEGadget<F>>::from_bits_le(&bits, cs)
    }
}

impl<F: Field> FromBytesBEGadget<F> for Address {
    fn from_bytes_be<CS: ConstraintSystem<F>>(bytes: &[UInt8], _cs: CS) -> Result<Address, SynthesisError> {
        if bytes.len() != 32 {
            return Err(SynthesisError::AssignmentMissing);
        }

        let bytes = bytes
            .into_iter()
            .rev()
            .map(|v| v.value.ok_or_else(|| SynthesisError::Unsatisfiable))
            .collect::<Result<Vec<u8>, SynthesisError>>()?;

        Self::constant(&bytes).map_err(|_| SynthesisError::Unsatisfiable)
    }

    fn from_bytes_be_strict<CS: ConstraintSystem<F>>(bytes: &[UInt8], cs: CS) -> Result<Address, SynthesisError> {
        <Self as FromBytesBEGadget<F>>::from_bytes_be(bytes, cs)
    }
}

impl<F: Field> FromBytesLEGadget<F> for Address {
    fn from_bytes_le<CS: ConstraintSystem<F>>(bytes: &[UInt8], _cs: CS) -> Result<Address, SynthesisError> {
        if bytes.len() != 32 {
            return Err(SynthesisError::AssignmentMissing);
        }

        let bytes = bytes
            .into_iter()
            .map(|v| v.value.ok_or_else(|| SynthesisError::Unsatisfiable))
            .collect::<Result<Vec<u8>, SynthesisError>>()?;

        Self::constant(&bytes).map_err(|_| SynthesisError::Unsatisfiable)
    }

    fn from_bytes_le_strict<CS: ConstraintSystem<F>>(bits: &[UInt8], cs: CS) -> Result<Address, SynthesisError> {
        <Self as FromBytesLEGadget<F>>::from_bytes_le(bits, cs)
    }
}

impl<F: PrimeField> ToBytesLEGadget<F> for Address {
    fn to_bytes_le<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        self.bytes.to_bytes_le(cs)
    }

    fn to_bytes_le_strict<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        self.bytes.to_bytes_le_strict(cs)
    }
}

impl<F: PrimeField> ToBytesBEGadget<F> for Address {
    fn to_bytes_be<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        self.bytes.to_bytes_be(cs)
    }

    fn to_bytes_be_strict<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        self.bytes.to_bytes_be_strict(cs)
    }
}

impl std::fmt::Display for Address {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.address)
    }
}
