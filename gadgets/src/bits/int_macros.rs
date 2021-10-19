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

macro_rules! to_bits_int_impl {
    ($name: ident) => {
        impl<F: Field> ToBitsBEGadget<F> for $name {
            fn to_bits_be<CS: ConstraintSystem<F>>(&self, _: CS) -> Result<Vec<Boolean>, SynthesisError> {
                let mut bits = self.bits.clone();
                bits.reverse();
                Ok(bits)
            }

            fn to_bits_be_strict<CS: ConstraintSystem<F>>(&self, _: CS) -> Result<Vec<Boolean>, SynthesisError> {
                let mut bits = self.bits.clone();
                bits.reverse();
                Ok(bits)
            }
        }

        impl<F: Field> ToBitsLEGadget<F> for $name {
            fn to_bits_le<CS: ConstraintSystem<F>>(&self, _: CS) -> Result<Vec<Boolean>, SynthesisError> {
                Ok(self.bits.clone())
            }

            fn to_bits_le_strict<CS: ConstraintSystem<F>>(&self, _: CS) -> Result<Vec<Boolean>, SynthesisError> {
                Ok(self.bits.clone())
            }
        }
    };
}

macro_rules! to_bytes_int_impl {
    ($name: ident, $size: expr) => {
        impl<F: Field> ToBytesBEGadget<F> for $name {
            #[inline]
            fn to_bytes_be<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
                let mut bytes = self.to_bytes_le(cs)?;
                bytes.reverse();
                Ok(bytes)
            }

            fn to_bytes_be_strict<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
                self.to_bytes_be(cs)
            }
        }

        impl<F: Field> ToBytesLEGadget<F> for $name {
            #[inline]
            fn to_bytes_le<CS: ConstraintSystem<F>>(&self, mut cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
                // 128 / 8 = 16, 64 / 8 = 8, 32 / 8 = 4, 16 / 8 = 2, 8 / 8 = 1
                const BYTES_SIZE: usize = $size / 8;

                let value_chunks = match self.value.map(|val| {
                    let mut bytes = [0u8; BYTES_SIZE];
                    val.write_le(bytes.as_mut()).unwrap();
                    bytes
                }) {
                    Some(chunks) => chunks
                        .to_vec()
                        .iter()
                        .map(|item| Some(item.clone()))
                        .collect::<Vec<Option<u8>>>(),
                    None => vec![None; BYTES_SIZE],
                };

                let bits = self.to_bits_le(&mut cs.ns(|| "to_bytes_le"))?;
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
                assert_eq!(bytes.capacity(), BYTES_SIZE);

                Ok(bytes)
            }

            fn to_bytes_le_strict<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
                self.to_bytes_le(cs)
            }
        }
    };
}

macro_rules! from_bits_int_impl {
    ($name: ident, $type_: ty, $utype: ty, $size_bits: expr) => {
        impl<F: Field> FromBitsBEGadget<F> for $name {
            fn from_bits_be<CS: ConstraintSystem<F>>(bits: &[Boolean], _: CS) -> Result<$name, SynthesisError> {
                let mut value = Some(0 as $utype);
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

            fn from_bits_be_strict<CS: ConstraintSystem<F>>(bits: &[Boolean], cs: CS) -> Result<$name, SynthesisError> {
                <Self as FromBitsBEGadget<F>>::from_bits_be(bits, cs)
            }
        }

        impl<F: Field> FromBitsLEGadget<F> for $name {
            fn from_bits_le<CS: ConstraintSystem<F>>(bits: &[Boolean], _: CS) -> Result<$name, SynthesisError> {
                let mut value = Some(0 as $utype);
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

            fn from_bits_le_strict<CS: ConstraintSystem<F>>(bits: &[Boolean], cs: CS) -> Result<$name, SynthesisError> {
                <Self as FromBitsLEGadget<F>>::from_bits_le(bits, cs)
            }
        }
    };

    ($name: ident, $type_: ty, $size_bits: expr) => {
        impl<F: Field> FromBitsBEGadget<F> for $name {
            fn from_bits_be<CS: ConstraintSystem<F>>(bits: &[Boolean], _: CS) -> Result<$name, SynthesisError> {
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

            fn from_bits_be_strict<CS: ConstraintSystem<F>>(bits: &[Boolean], cs: CS) -> Result<$name, SynthesisError> {
                <Self as FromBitsBEGadget<F>>::from_bits_be(bits, cs)
            }
        }
        impl<F: Field> FromBitsLEGadget<F> for $name {
            fn from_bits_le<CS: ConstraintSystem<F>>(bits: &[Boolean], _: CS) -> Result<$name, SynthesisError> {
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

            fn from_bits_le_strict<CS: ConstraintSystem<F>>(bits: &[Boolean], cs: CS) -> Result<$name, SynthesisError> {
                <Self as FromBitsLEGadget<F>>::from_bits_le(bits, cs)
            }
        }
    };
}

macro_rules! from_bytes_int_impl {
    (UInt8, u8, 8) => {
        impl<F: Field> FromBytesBEGadget<F, 1> for UInt8 {
            fn from_bytes_be<CS: ConstraintSystem<F>>(bytes: &[UInt8; 1], _: CS) -> Result<Self, SynthesisError> {
                Ok(bytes[0].clone())
            }

            fn from_bytes_be_strict<CS: ConstraintSystem<F>>(
                bytes: &[UInt8; 1],
                _: CS,
            ) -> Result<Self, SynthesisError> {
                Ok(bytes[0].clone())
            }
        }

        impl<F: Field> FromBytesLEGadget<F, 1> for UInt8 {
            fn from_bytes_le<CS: ConstraintSystem<F>>(bytes: &[UInt8; 1], _: CS) -> Result<Self, SynthesisError> {
                Ok(bytes[0].clone())
            }

            fn from_bytes_le_strict<CS: ConstraintSystem<F>>(
                bytes: &[UInt8; 1],
                _: CS,
            ) -> Result<Self, SynthesisError> {
                Ok(bytes[0].clone())
            }
        }
    };

    ($name: ident, $type_: ty, $size_bytes: expr) => {
        impl<F: Field> FromBytesBEGadget<F> for $name {
            fn from_bytes_be<CS: ConstraintSystem<F>>(bytes: &[UInt8], cs: CS) -> Result<Self, SynthesisError> {
                let bits = bytes
                    .iter()
                    .rev()
                    .flat_map(|byte| byte.u8_to_bits_le())
                    .collect::<Vec<_>>();

                Self::from_bits_le(&bits, cs)
            }

            fn from_bytes_be_strict<CS: ConstraintSystem<F>>(bytes: &[UInt8], cs: CS) -> Result<Self, SynthesisError> {
                Self::from_bytes_be(bytes, cs)
            }
        }

        impl<F: Field> FromBytesLEGadget<F> for $name {
            fn from_bytes_le<CS: ConstraintSystem<F>>(bytes: &[UInt8], cs: CS) -> Result<Self, SynthesisError> {
                let bits = bytes
                    .iter()
                    .flat_map(|byte| byte.u8_to_bits_le())
                    .collect::<Vec<_>>();

                Self::from_bits_le(&bits, cs)
            }

            fn from_bytes_le_strict<CS: ConstraintSystem<F>>(bytes: &[UInt8], cs: CS) -> Result<Self, SynthesisError> {
                Self::from_bytes_le(bytes, cs)
            }
        }
    };
}
