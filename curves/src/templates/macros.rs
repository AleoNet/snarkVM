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

// https://github.com/rust-lang/rust/issues/57966 forces us to export these and
// import them via `use crate::` syntax. It'd be nice if we were able to avoid any
// macro_use/macro_export and just import the macro
#[macro_export]
macro_rules! impl_sw_curve_serializer {
    ($params: ident) => {
        // Projective Group point implementations delegate to the Affine version
        impl<P: $params> CanonicalSerialize for Projective<P> {
            #[allow(unused_qualifications)]
            #[inline]
            fn serialize<W: snarkvm_utilities::io::Write>(
                &self,
                writer: &mut W,
            ) -> Result<(), snarkvm_utilities::serialize::SerializationError> {
                CanonicalSerialize::serialize(&Affine::<P>::from(*self), writer)
            }

            #[allow(unused_qualifications)]
            fn serialize_uncompressed<W: snarkvm_utilities::io::Write>(
                &self,
                writer: &mut W,
            ) -> Result<(), snarkvm_utilities::serialize::SerializationError> {
                CanonicalSerialize::serialize_uncompressed(&Affine::<P>::from(*self), writer)
            }

            #[inline]
            fn serialized_size(&self) -> usize {
                Affine::<P>::from(*self).serialized_size()
            }

            #[inline]
            fn uncompressed_size(&self) -> usize {
                Affine::<P>::from(*self).uncompressed_size()
            }
        }

        impl<P: $params> CanonicalDeserialize for Projective<P> {
            #[allow(unused_qualifications)]
            fn deserialize<R: snarkvm_utilities::io::Read>(
                reader: &mut R,
            ) -> Result<Self, snarkvm_utilities::serialize::SerializationError> {
                let el: Affine<P> = CanonicalDeserialize::deserialize(reader)?;
                Ok(el.into())
            }

            #[allow(unused_qualifications)]
            fn deserialize_uncompressed<R: snarkvm_utilities::io::Read>(
                reader: &mut R,
            ) -> Result<Self, snarkvm_utilities::serialize::SerializationError> {
                let el: Affine<P> = CanonicalDeserialize::deserialize_uncompressed(reader)?;
                Ok(el.into())
            }
        }

        impl<P: $params> ConstantSerializedSize for Projective<P> {
            const SERIALIZED_SIZE: usize = <P::BaseField as ConstantSerializedSize>::SERIALIZED_SIZE;
            const UNCOMPRESSED_SIZE: usize = 2 * <P::BaseField as ConstantSerializedSize>::SERIALIZED_SIZE;
        }

        impl<P: $params> CanonicalSerialize for Affine<P> {
            #[allow(unused_qualifications)]
            #[inline]
            fn serialize<W: snarkvm_utilities::io::Write>(
                &self,
                writer: &mut W,
            ) -> Result<(), snarkvm_utilities::serialize::SerializationError> {
                if self.is_zero() {
                    let flags = snarkvm_utilities::serialize::SWFlags::infinity();
                    // Serialize 0.
                    P::BaseField::zero().serialize_with_flags(writer, flags)
                } else {
                    let flags = snarkvm_utilities::serialize::SWFlags::from_y_sign(self.y > -self.y);
                    self.x.serialize_with_flags(writer, flags)
                }
            }

            #[inline]
            fn serialized_size(&self) -> usize {
                Self::SERIALIZED_SIZE
            }

            #[allow(unused_qualifications)]
            #[inline]
            fn serialize_uncompressed<W: snarkvm_utilities::io::Write>(
                &self,
                writer: &mut W,
            ) -> Result<(), snarkvm_utilities::serialize::SerializationError> {
                let flags = if self.is_zero() {
                    snarkvm_utilities::serialize::SWFlags::infinity()
                } else {
                    snarkvm_utilities::serialize::SWFlags::default()
                };
                CanonicalSerialize::serialize(&self.x, writer)?;
                self.y.serialize_with_flags(writer, flags)?;
                Ok(())
            }

            #[inline]
            fn uncompressed_size(&self) -> usize {
                Self::UNCOMPRESSED_SIZE
            }
        }

        impl<P: $params> ConstantSerializedSize for Affine<P> {
            const SERIALIZED_SIZE: usize = <P::BaseField as ConstantSerializedSize>::SERIALIZED_SIZE;
            const UNCOMPRESSED_SIZE: usize = 2 * <P::BaseField as ConstantSerializedSize>::SERIALIZED_SIZE;
        }

        impl<P: $params> CanonicalDeserialize for Affine<P> {
            #[allow(unused_qualifications)]
            fn deserialize<R: snarkvm_utilities::io::Read>(
                reader: &mut R,
            ) -> Result<Self, snarkvm_utilities::serialize::SerializationError> {
                let (x, flags): (P::BaseField, snarkvm_utilities::serialize::SWFlags) =
                    CanonicalDeserializeWithFlags::deserialize_with_flags(reader)?;
                if flags.is_infinity() {
                    Ok(Self::zero())
                } else {
                    let p = Affine::<P>::from_x_coordinate(x, flags.is_positive().unwrap())
                        .ok_or(snarkvm_utilities::serialize::SerializationError::InvalidData)?;
                    if !snarkvm_utilities::PROCESSING_SNARK_PARAMS
                        .with(|p| p.load(std::sync::atomic::Ordering::Relaxed))
                    {
                        if !p.is_in_correct_subgroup_assuming_on_curve() {
                            return Err(snarkvm_utilities::serialize::SerializationError::InvalidData);
                        }
                    } else {
                        snarkvm_utilities::SNARK_PARAMS_AFFINE_COUNT
                            .with(|p| p.fetch_add(1, std::sync::atomic::Ordering::Relaxed));
                    }
                    Ok(p)
                }
            }

            #[allow(unused_qualifications)]
            fn deserialize_uncompressed<R: snarkvm_utilities::io::Read>(
                reader: &mut R,
            ) -> Result<Self, snarkvm_utilities::serialize::SerializationError> {
                let x: P::BaseField = CanonicalDeserialize::deserialize(reader)?;
                let (y, flags): (P::BaseField, snarkvm_utilities::serialize::SWFlags) =
                    CanonicalDeserializeWithFlags::deserialize_with_flags(reader)?;

                let p = Affine::<P>::new(x, y, flags.is_infinity());
                if !p.is_in_correct_subgroup_assuming_on_curve() {
                    return Err(snarkvm_utilities::serialize::SerializationError::InvalidData);
                }
                Ok(p)
            }
        }
    };
}

#[macro_export]
macro_rules! impl_edwards_curve_serializer {
    ($params: ident) => {
        impl<P: $params> CanonicalSerialize for Projective<P> {
            #[allow(unused_qualifications)]
            #[inline]
            fn serialize<W: snarkvm_utilities::io::Write>(
                &self,
                writer: &mut W,
            ) -> Result<(), snarkvm_utilities::serialize::SerializationError> {
                CanonicalSerialize::serialize(&Affine::<P>::from(*self), writer)
            }

            #[allow(unused_qualifications)]
            fn serialize_uncompressed<W: snarkvm_utilities::io::Write>(
                &self,
                writer: &mut W,
            ) -> Result<(), snarkvm_utilities::serialize::SerializationError> {
                CanonicalSerialize::serialize_uncompressed(&Affine::<P>::from(*self), writer)
            }

            #[inline]
            fn serialized_size(&self) -> usize {
                Affine::<P>::from(*self).serialized_size()
            }

            #[inline]
            fn uncompressed_size(&self) -> usize {
                Affine::<P>::from(*self).uncompressed_size()
            }
        }

        impl<P: $params> ConstantSerializedSize for Projective<P> {
            const SERIALIZED_SIZE: usize = <P::BaseField as ConstantSerializedSize>::SERIALIZED_SIZE;
            const UNCOMPRESSED_SIZE: usize = 2 * <P::BaseField as ConstantSerializedSize>::SERIALIZED_SIZE;
        }

        impl<P: $params> CanonicalDeserialize for Projective<P> {
            #[allow(unused_qualifications)]
            fn deserialize<R: snarkvm_utilities::io::Read>(
                reader: &mut R,
            ) -> Result<Self, snarkvm_utilities::serialize::SerializationError> {
                let el: Affine<P> = CanonicalDeserialize::deserialize(reader)?;
                Ok(el.into())
            }

            #[allow(unused_qualifications)]
            fn deserialize_uncompressed<R: snarkvm_utilities::io::Read>(
                reader: &mut R,
            ) -> Result<Self, snarkvm_utilities::serialize::SerializationError> {
                let el: Affine<P> = CanonicalDeserialize::deserialize_uncompressed(reader)?;
                Ok(el.into())
            }
        }

        impl<P: $params> CanonicalSerialize for Affine<P> {
            #[allow(unused_qualifications)]
            #[inline]
            fn serialize<W: snarkvm_utilities::io::Write>(
                &self,
                writer: &mut W,
            ) -> Result<(), snarkvm_utilities::serialize::SerializationError> {
                if self.is_zero() {
                    let flags = snarkvm_utilities::serialize::EdwardsFlags::default();
                    // Serialize 0.
                    P::BaseField::zero().serialize_with_flags(writer, flags)
                } else {
                    let flags = snarkvm_utilities::serialize::EdwardsFlags::from_y_sign(self.y > -self.y);
                    self.x.serialize_with_flags(writer, flags)
                }
            }

            #[inline]
            fn serialized_size(&self) -> usize {
                Self::SERIALIZED_SIZE
            }

            #[allow(unused_qualifications)]
            #[inline]
            fn serialize_uncompressed<W: snarkvm_utilities::io::Write>(
                &self,
                writer: &mut W,
            ) -> Result<(), snarkvm_utilities::serialize::SerializationError> {
                self.x.serialize_uncompressed(writer)?;
                self.y.serialize_uncompressed(writer)?;
                Ok(())
            }

            #[inline]
            fn uncompressed_size(&self) -> usize {
                Self::UNCOMPRESSED_SIZE
            }
        }

        impl<P: $params> ConstantSerializedSize for Affine<P> {
            const SERIALIZED_SIZE: usize = <P::BaseField as ConstantSerializedSize>::SERIALIZED_SIZE;
            const UNCOMPRESSED_SIZE: usize = 2 * <P::BaseField as ConstantSerializedSize>::SERIALIZED_SIZE;
        }

        impl<P: $params> CanonicalDeserialize for Affine<P> {
            #[allow(unused_qualifications)]
            fn deserialize<R: snarkvm_utilities::io::Read>(
                reader: &mut R,
            ) -> Result<Self, snarkvm_utilities::serialize::SerializationError> {
                let (x, flags): (P::BaseField, snarkvm_utilities::serialize::EdwardsFlags) =
                    CanonicalDeserializeWithFlags::deserialize_with_flags(reader)?;
                if x == P::BaseField::zero() {
                    Ok(Self::zero())
                } else {
                    let p = Affine::<P>::from_x_coordinate(x, flags.is_positive())
                        .ok_or(snarkvm_utilities::serialize::SerializationError::InvalidData)?;
                    if !p.is_in_correct_subgroup_assuming_on_curve() {
                        return Err(snarkvm_utilities::serialize::SerializationError::InvalidData);
                    }
                    Ok(p)
                }
            }

            #[allow(unused_qualifications)]
            fn deserialize_uncompressed<R: snarkvm_utilities::io::Read>(
                reader: &mut R,
            ) -> Result<Self, snarkvm_utilities::serialize::SerializationError> {
                let x: P::BaseField = CanonicalDeserialize::deserialize(reader)?;
                let y: P::BaseField = CanonicalDeserialize::deserialize(reader)?;

                let p = Affine::<P>::new(x, y);
                if !p.is_in_correct_subgroup_assuming_on_curve() {
                    return Err(snarkvm_utilities::serialize::SerializationError::InvalidData);
                }
                Ok(p)
            }
        }
    };
}
