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

macro_rules! to_bits_le_int_impl {
    ($name: ident) => {
        impl<F: Field> ToBitsLEGadget<F> for $name {
            fn to_bits_le<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<Boolean>, SynthesisError> {
                self.bits.to_bits_le(cs)
            }

            fn to_bits_le_strict<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<Boolean>, SynthesisError> {
                self.bits.to_bits_le(cs)
            }
        }
    };
}

macro_rules! to_bits_be_int_impl {
    ($name: ident) => {
        impl<F: Field> ToBitsBEGadget<F> for $name {
            fn to_bits_be<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<Boolean>, SynthesisError> {
                self.bits.to_bits_be(cs)
            }

            fn to_bits_be_strict<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<Boolean>, SynthesisError> {
                self.bits.to_bits_be(cs)
            }
        }
    };
}

macro_rules! from_bits_le_int_impl {
    ($name: ident, $type_: ty, $utype_: ty, $size: expr) => {
        impl<F: Field> FromBitsLEGadget<F> for $name {
            fn from_bits_le(&self, bits: Vec<Boolean>) -> Result<$name, SynthesisError> {
                let mut value = Some(0 as $utype_);
                for b in bits.iter().rev() {
                    value.as_mut().map(|v| *v <<= 1);

                    match *b {
                        Boolean::Constant(b) => {
                            if b {
                                value.as_mut().map(|v| *v |= 1);
                            }
                        }
                        Boolean::Is(ref b) => match b.get_value() {
                            Some(true) => {
                                value.as_mut().map(|v| *v |= 1);
                            }
                            Some(false) => {}
                            None => value = None,
                        },
                        Boolean::Not(ref b) => match b.get_value() {
                            Some(false) => {
                                value.as_mut().map(|v| *v |= 1);
                            }
                            Some(true) => {}
                            None => value = None,
                        },
                    }
                }

                Ok(Self {
                    value: value.map(|x| x as $type_),
                    bits,
                })
            }

            fn from_bits_le_strict(&self, bits: Vec<Boolean>) -> Result<$name, SynthesisError> {
                if bits.len() != $size {
                    return Err(SynthesisError::Unsatisfiable);
                }

                todo!()
            }
        }
    };
}

macro_rules! from_bits_be_int_impl {
    ($name: ident, $type_: ty, $utype_: ty, $size: expr) => {
        impl<F: Field> FromBitsBEGadget<F> for $name {
            fn from_bits_be(&self, bits: Vec<Boolean>) -> Result<$name, SynthesisError> {
                if bits.len() != $size {
                    return Err(SynthesisError::Unsatisfiable);
                }

                todo!()
            }

            fn from_bits_be_strict(&self, bits: Vec<Boolean>) -> Result<$name, SynthesisError> {
                if bits.len() != $size {
                    return Err(SynthesisError::Unsatisfiable);
                }

                todo!()
            }
        }
    };
}
