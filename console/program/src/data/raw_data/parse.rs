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

use super::*;

static DATA_PREFIX: &str = "data";

impl<N: Network> Parser for Data<N> {
    /// Parses a string into a `Data`.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Prepare a parser for the `Data`.
        let parse_data = recognize(pair(
            pair(tag(DATA_PREFIX), tag("1")),
            many1(terminated(one_of("qpzry9x8gf2tvdw0s3jn54khce6mua7l"), many0(char('_')))),
        ));

        // Parse the data from the string.
        map_res(parse_data, |data: &str| -> Result<_, Error> { Self::from_str(&data.replace('_', "")) })(string)
    }
}

impl<N: Network> FromStr for Data<N> {
    type Err = Error;

    /// Reads in the `Data` string.
    fn from_str(data_string: &str) -> Result<Self, Self::Err> {
        // Decode the `Data` string from bech32m.
        let (hrp, data, variant) = bech32::decode(data_string)?;
        if hrp != DATA_PREFIX {
            bail!("Failed to decode `Data`: '{hrp}' is an invalid prefix")
        } else if data.is_empty() {
            bail!("Failed to decode `Data`: data field is empty")
        } else if variant != bech32::Variant::Bech32m {
            bail!("Found a `Data` that is not bech32m encoded: {data_string}");
        }
        // Decode the data from u5 to u8, and into the `Data` object.
        Ok(Self::encode_from_bytes_le(&Vec::from_base32(&data)?[..])?)
    }
}

impl<N: Network> Debug for Data<N> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for Data<N> {
    /// Writes the `Data` as a bech32m string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        // Decode the `Data` as bytes.
        let bytes = self.decode_as_bytes_le().map_err(|_| fmt::Error)?;
        // Encode the bytes into bech32m.
        let string =
            bech32::encode(DATA_PREFIX, bytes.to_base32(), bech32::Variant::Bech32m).map_err(|_| fmt::Error)?;
        // Output the string.
        Display::fmt(&string, f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network::MainnetV0;

    type CurrentNetwork = MainnetV0;

    const ITERATIONS: u64 = 1_000;

    #[test]
    fn test_parse() -> Result<()> {
        // Ensure type and empty value fails.
        assert!(Data::<CurrentNetwork>::parse(&format!("{DATA_PREFIX}1")).is_err());
        assert!(Data::<CurrentNetwork>::parse("").is_err());

        let mut rng = TestRng::default();

        for _ in 0..ITERATIONS {
            // Sample a new `Data`.
            let data = Data::<CurrentNetwork>((0..100).map(|_| Uniform::rand(&mut rng)).collect::<Vec<_>>());

            let expected = format!("{data}");
            let (remainder, candidate) = Data::<CurrentNetwork>::parse(&expected).unwrap();
            assert_eq!(format!("{expected}"), candidate.to_string());
            assert_eq!(DATA_PREFIX, candidate.to_string().split('1').next().unwrap());
            assert_eq!("", remainder);
        }
        Ok(())
    }

    #[test]
    fn test_string() -> Result<()> {
        let mut rng = TestRng::default();

        for _ in 0..ITERATIONS {
            // Sample a new `Data`.
            let expected = Data::<CurrentNetwork>((0..100).map(|_| Uniform::rand(&mut rng)).collect::<Vec<_>>());

            // Check the string representation.
            let candidate = format!("{expected}");
            assert_eq!(expected, Data::from_str(&candidate)?);
            assert_eq!(DATA_PREFIX, candidate.to_string().split('1').next().unwrap());
        }
        Ok(())
    }

    #[test]
    fn test_display() -> Result<()> {
        let mut rng = TestRng::default();

        for _ in 0..ITERATIONS {
            // Sample a new `Data`.
            let expected = Data::<CurrentNetwork>((0..100).map(|_| Uniform::rand(&mut rng)).collect::<Vec<_>>());

            let candidate = expected.to_string();
            assert_eq!(format!("{expected}"), candidate);
            assert_eq!(DATA_PREFIX, candidate.split('1').next().unwrap());

            let candidate_recovered = Data::<CurrentNetwork>::from_str(&candidate.to_string())?;
            assert_eq!(expected, candidate_recovered);
        }
        Ok(())
    }

    #[test]
    fn test_parse_end_to_end() {
        // [0u8]
        let bytes = [0u8];
        let data = Data::<MainnetV0>::encode_from_bytes_le(&bytes).unwrap();
        let string = data.to_string();
        assert_eq!(string, "data1qqk73cky");
        let data_from_string = Data::<MainnetV0>::from_str(&string).unwrap();
        assert_eq!(data, data_from_string);
        let decoded_bytes = data_from_string.decode_as_bytes_le().unwrap();
        assert_eq!(bytes.to_vec(), decoded_bytes);

        // [1u8]
        let bytes = [1u8];
        let data = Data::<MainnetV0>::encode_from_bytes_le(&bytes).unwrap();
        let string = data.to_string();
        assert_eq!(string, "data1qye5n7e7");
        let data_from_string = Data::<MainnetV0>::from_str(&string).unwrap();
        assert_eq!(data, data_from_string);
        let decoded_bytes = data_from_string.decode_as_bytes_le().unwrap();
        assert_eq!(bytes.to_vec(), decoded_bytes);

        // [0u8, 0u8]
        let bytes = [0u8, 0u8];
        let data = Data::<MainnetV0>::encode_from_bytes_le(&bytes).unwrap();
        let string = data.to_string();
        assert_eq!(string, "data1qqqqkrn0ty");
        let data_from_string = Data::<MainnetV0>::from_str(&string).unwrap();
        assert_eq!(data, data_from_string);
        let decoded_bytes = data_from_string.decode_as_bytes_le().unwrap();
        assert_eq!(bytes.to_vec(), decoded_bytes);

        // [0u8, 1u8]
        let bytes = [0u8, 1u8];
        let data = Data::<MainnetV0>::encode_from_bytes_le(&bytes).unwrap();
        let string = data.to_string();
        assert_eq!(string, "data1qqqsrzmh7h");
        let data_from_string = Data::<MainnetV0>::from_str(&string).unwrap();
        assert_eq!(data, data_from_string);
        let decoded_bytes = data_from_string.decode_as_bytes_le().unwrap();
        assert_eq!(bytes.to_vec(), decoded_bytes);

        // [1u8, 0u8]
        let bytes = [1u8, 0u8];
        let data = Data::<MainnetV0>::encode_from_bytes_le(&bytes).unwrap();
        let string = data.to_string();
        assert_eq!(string, "data1qyqq7t7p5l");
        let data_from_string = Data::<MainnetV0>::from_str(&string).unwrap();
        assert_eq!(data, data_from_string);
        let decoded_bytes = data_from_string.decode_as_bytes_le().unwrap();
        assert_eq!(bytes.to_vec(), decoded_bytes);

        // [1u8, 1u8]
        let bytes = [1u8, 1u8];
        let data = Data::<MainnetV0>::encode_from_bytes_le(&bytes).unwrap();
        let string = data.to_string();
        assert_eq!(string, "data1qyqst2kepv");
        let data_from_string = Data::<MainnetV0>::from_str(&string).unwrap();
        assert_eq!(data, data_from_string);
        let decoded_bytes = data_from_string.decode_as_bytes_le().unwrap();
        assert_eq!(bytes.to_vec(), decoded_bytes);

        // "hello"
        let bytes = "hello".as_bytes();
        let data = Data::<MainnetV0>::encode_from_bytes_le(bytes).unwrap();
        let string = data.to_string();
        assert_eq!(string, "data1dpjkcmr049vt4z");
        let data_from_string = Data::<MainnetV0>::from_str(&string).unwrap();
        assert_eq!(data, data_from_string);
        let decoded_bytes = data_from_string.decode_as_bytes_le().unwrap();
        assert_eq!(bytes.to_vec(), decoded_bytes);

        // "world"
        let bytes = "world".as_bytes();
        let data = Data::<MainnetV0>::encode_from_bytes_le(bytes).unwrap();
        let string = data.to_string();
        assert_eq!(string, "data1wahhymry9kmx0s");
        let data_from_string = Data::<MainnetV0>::from_str(&string).unwrap();
        assert_eq!(data, data_from_string);
        let decoded_bytes = data_from_string.decode_as_bytes_le().unwrap();
        assert_eq!(bytes.to_vec(), decoded_bytes);

        // "hello world"
        let bytes = "hello world".as_bytes();
        let data = Data::<MainnetV0>::encode_from_bytes_le(bytes).unwrap();
        let string = data.to_string();
        assert_eq!(string, "data1dpjkcmr0ypmk7unvvs2rhz3v");
        let data_from_string = Data::<MainnetV0>::from_str(&string).unwrap();
        assert_eq!(data, data_from_string);
        let decoded_bytes = data_from_string.decode_as_bytes_le().unwrap();
        assert_eq!(bytes.to_vec(), decoded_bytes);
    }
}
