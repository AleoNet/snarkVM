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

macro_rules! to_bytes_int_impl {
    ($name: ident, $size: expr) => {
        impl<F: Field> ToBytesGadget<F> for $name {
            #[inline]
            fn to_bytes<CS: ConstraintSystem<F>>(&self, mut cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
                // 128 / 8 = 16, 64 / 8 = 8, 32 / 8 = 4, 16 / 8 = 2, 8 / 8 = 1
                const BYTES_SIZE: usize = $size / 8;

                let value_chunks = match self.value.map(|val| {
                    let mut bytes = [0u8; BYTES_SIZE];
                    val.write_le(bytes.as_mut()).unwrap();
                    bytes
                }) {
                    Some(chunks) => [Some(chunks[0]), Some(chunks[1]), Some(chunks[2]), Some(chunks[3])],
                    None => [None, None, None, None],
                };

                let bits = self.to_bits_le(&mut cs.ns(|| "to_bits_le"))?;
                let bytes = bits
                    .chunks(8)
                    .into_iter()
                    .zip(value_chunks.iter())
                    .map(|(chunk8, value)| UInt8 {
                        bits: chunk8.to_vec(),
                        negated: false,
                        value: *value,
                    })
                    .collect::<Vec<UInt8>>();
                assert_eq!(bytes.capacity(), 8);

                Ok(bytes)
            }

            fn to_bytes_strict<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
                self.to_bytes(cs)
            }
        }
    };
}

macro_rules! from_bits_le_int_impl {
    ($name: ident, $type_: ty, $utype_: ty, $size: expr) => {
        impl FromBitsLEGadget for $name {
            fn from_bits_le(bits: &[Boolean]) -> Result<$name, SynthesisError> {
                if bits.len() != $size {
                    return Err(SynthesisError::Unsatisfiable);
                }

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
                    bits: bits.to_vec(),
                })
            }

            fn from_bits_le_strict(bits: &[Boolean]) -> Result<$name, SynthesisError> {
                <Self as FromBitsLEGadget>::from_bits_le(bits)
            }
        }
    };
    ($name: ident, $type_: ty, $size: expr) => {
        impl FromBitsLEGadget for $name {
            fn from_bits_le(bits: &[Boolean]) -> Result<$name, SynthesisError> {
                if bits.len() != $size {
                    return Err(SynthesisError::Unsatisfiable);
                }

                let mut value = Some(0 as $type_);
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
                    negated: false,
                    bits: bits.to_vec(),
                })
            }

            fn from_bits_le_strict(bits: &[Boolean]) -> Result<$name, SynthesisError> {
                <Self as FromBitsLEGadget>::from_bits_le(bits)
            }
        }
    };
}

macro_rules! from_bits_be_int_impl {
    ($name: ident, $type_: ty, $utype_: ty, $size: expr) => {
        impl FromBitsBEGadget for $name {
            fn from_bits_be(bits: &[Boolean]) -> Result<$name, SynthesisError> {
                if bits.len() != $size {
                    return Err(SynthesisError::Unsatisfiable);
                }

                let mut value = Some(0 as $utype_);
                for b in bits.iter() {
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
                    bits: bits.to_vec(),
                })
            }

            fn from_bits_be_strict(bits: &[Boolean]) -> Result<$name, SynthesisError> {
                <Self as FromBitsBEGadget>::from_bits_be(bits)
            }
        }
    };
    ($name: ident, $type_: ty, $size: expr) => {
        impl FromBitsBEGadget for $name {
            fn from_bits_be(bits: &[Boolean]) -> Result<$name, SynthesisError> {
                if bits.len() != $size {
                    return Err(SynthesisError::Unsatisfiable);
                }

                let mut value = Some(0 as $type_);
                for b in bits.iter() {
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
                    negated: false,
                    bits: bits.to_vec(),
                })
            }

            fn from_bits_be_strict(bits: &[Boolean]) -> Result<$name, SynthesisError> {
                <Self as FromBitsBEGadget>::from_bits_be(bits)
            }
        }
    };
}
