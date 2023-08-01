// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use console::prelude::*;

use ::bytes::Bytes;

const PREFIX: &str = "data";

/// This object enables deferred deserialization / ahead-of-time serialization for objects that
/// take a while to deserialize / serialize, in order to allow these operations to be non-blocking.
#[derive(Clone, PartialEq, Eq)]
pub enum Data<T: FromBytes + ToBytes + Send + 'static> {
    Object(T),
    Buffer(Bytes),
}

impl<T: FromBytes + ToBytes + Send + 'static> Data<T> {
    pub fn into<T2: From<Data<T>> + From<T> + FromBytes + ToBytes + Send + 'static>(self) -> Data<T2> {
        match self {
            Self::Object(x) => Data::Object(x.into()),
            Self::Buffer(bytes) => Data::Buffer(bytes),
        }
    }

    pub fn deserialize_blocking(self) -> Result<T> {
        match self {
            Self::Object(x) => Ok(x),
            Self::Buffer(bytes) => T::from_bytes_le(&bytes),
        }
    }

    pub fn serialize_blocking_into<W: Write>(&self, writer: &mut W) -> Result<()> {
        match self {
            Self::Object(x) => Ok(writer.write_all(&x.to_bytes_le()?)?),
            Self::Buffer(bytes) => Ok(writer.write_all(bytes)?),
        }
    }
}

impl<T: FromBytes + ToBytes + DeserializeOwned + Send + 'static> FromStr for Data<T> {
    type Err = Error;

    /// Initializes the data from a JSON-string.
    fn from_str(data: &str) -> Result<Self, Self::Err> {
        Ok(serde_json::from_str(data)?)
    }
}

impl<T: FromBytes + ToBytes + Serialize + Send + 'static> Debug for Data<T> {
    /// Prints the data as a JSON-string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<T: FromBytes + ToBytes + Serialize + Send + 'static> Display for Data<T> {
    /// Displays the data as a JSON-string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", serde_json::to_string(self).map_err::<fmt::Error, _>(ser::Error::custom)?)
    }
}

impl<T: FromBytes + ToBytes + Send + 'static> FromBytes for Data<T> {
    /// Reads the data from the buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the variant.
        let variant = u8::read_le(&mut reader)?;
        // Match the variant.
        match variant {
            0 => {
                // Read the object.
                let object = T::read_le(&mut reader)?;
                // Return the object.
                Ok(Self::Object(object))
            }
            1 => {
                // Read the number of bytes.
                let num_bytes = u32::read_le(&mut reader)?;
                // Read the bytes.
                let bytes = (0..num_bytes).map(|_| u8::read_le(&mut reader)).collect::<IoResult<Vec<u8>>>()?;
                // Return the data.
                Ok(Self::Buffer(Bytes::from(bytes)))
            }
            2.. => Err(error("Invalid data variant")),
        }
    }
}

impl<T: FromBytes + ToBytes + Send + 'static> ToBytes for Data<T> {
    /// Writes the data to the buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Write the data.
        match self {
            Self::Object(object) => {
                // Write the variant.
                0u8.write_le(&mut writer)?;
                // Write the object.
                object.write_le(&mut writer)
            }
            Self::Buffer(buffer) => {
                // Write the variant.
                1u8.write_le(&mut writer)?;
                // Write the number of bytes.
                u32::try_from(buffer.len()).map_err(|e| error(e.to_string()))?.write_le(&mut writer)?;
                // Write the bytes.
                writer.write_all(buffer)
            }
        }
    }
}

impl<T: FromBytes + ToBytes + Serialize + Send + 'static> Serialize for Data<T> {
    /// Serializes the data to a JSON-string or buffer.
    #[inline]
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => {
                let mut data = serializer.serialize_struct("Data", 2)?;
                match self {
                    Self::Object(object) => {
                        data.serialize_field("type", "object")?;
                        data.serialize_field("data", object)?;
                    }
                    Self::Buffer(buffer) => {
                        use console::prelude::ser::Error;

                        data.serialize_field("type", "buffer")?;

                        // Encode to bech32m.
                        let buffer = bech32::encode(PREFIX, buffer.to_vec().to_base32(), bech32::Variant::Bech32m)
                            .map_err(|_| S::Error::custom("Failed to encode data into bech32m"))?;

                        // Add the bech32m string.
                        data.serialize_field("data", &buffer)?;
                    }
                }
                data.end()
            }
            false => ToBytesSerializer::serialize_with_size_encoding(self, serializer),
        }
    }
}

impl<'de, T: FromBytes + ToBytes + DeserializeOwned + Send + 'static> Deserialize<'de> for Data<T> {
    /// Deserializes the data from a JSON-string or buffer.
    #[inline]
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => {
                let mut data = serde_json::Value::deserialize(deserializer)?;
                let type_: String = DeserializeExt::take_from_value::<D>(&mut data, "type")?;

                // Recover the data.
                match type_.as_str() {
                    "object" => {
                        let object = DeserializeExt::take_from_value::<D>(&mut data, "data")?;
                        Ok(Self::Object(object))
                    }
                    "buffer" => {
                        let encoding: String = DeserializeExt::take_from_value::<D>(&mut data, "data")?;

                        // Decode from bech32m.
                        let (hrp, data, variant) = bech32::decode(&encoding).map_err(de::Error::custom)?;
                        if hrp != PREFIX {
                            return Err(error(format!("Invalid data HRP - {hrp}"))).map_err(de::Error::custom);
                        };
                        if data.is_empty() {
                            return Err(error("Invalid bech32m data (empty)")).map_err(de::Error::custom);
                        }
                        if variant != bech32::Variant::Bech32m {
                            return Err(error("Invalid data - variant is not bech32m")).map_err(de::Error::custom);
                        }
                        Ok(Self::Buffer(Bytes::from(Vec::from_base32(&data).map_err(de::Error::custom)?)))
                    }
                    _ => Err(error(format!("Invalid data type - {type_}"))).map_err(de::Error::custom),
                }
            }
            false => FromBytesDeserializer::<Self>::deserialize_with_size_encoding(deserializer, "data"),
        }
    }
}
