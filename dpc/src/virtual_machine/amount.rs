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

use snarkvm_utilities::{FromBytes, ToBytes};

use anyhow::{anyhow, Result};
use serde::{Deserialize, Serialize};
use std::{
    fmt,
    io::{Read, Result as IoResult, Write},
    iter::Sum,
    ops::{Add, AddAssign, Sub, SubAssign},
};

/// Represents the amount of ALEOs.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct Amount(pub i64);

pub enum Denomination {
    /// AG
    GATE,
    /// ALEO
    CREDIT,
}

impl Denomination {
    /// The number of decimal places more than a Unit.
    fn precision(self) -> u32 {
        match self {
            Denomination::GATE => 0,
            Denomination::CREDIT => 6,
        }
    }
}

impl fmt::Display for Denomination {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", match self {
            Denomination::GATE => "AG",
            Denomination::CREDIT => "ALEO",
        })
    }
}

impl Amount {
    /// Exactly one Aleo credit (ALEO).
    pub const ONE_CREDIT: Amount = Amount(1_000_000i64);
    /// Exactly one Aleo gate (AG).
    pub const ONE_GATE: Amount = Amount(1i64);
    /// The zero amount.
    pub const ZERO: Amount = Amount(0i64);

    /// Create an `Amount` given a number of gates.
    pub fn from_gate(gates: i64) -> Self {
        Self(gates)
    }

    /// Create an `Amount` given a number of credits.
    pub fn from_aleo(aleo_value: i64) -> Self {
        Self::from_gate(aleo_value * 10_i64.pow(Denomination::CREDIT.precision()))
    }

    /// Add the values of two `Amount`s
    #[allow(clippy::should_implement_trait)]
    pub fn add(self, b: Self) -> Result<Self> {
        self.0.checked_add(b.0).ok_or(anyhow!("Amount addition overflow.")).map(Self::from_gate)
    }

    /// Subtract the value of two `Amount`
    #[allow(clippy::should_implement_trait)]
    pub fn sub(self, b: Self) -> Result<Self> {
        self.0.checked_sub(b.0).ok_or(anyhow!("Amount subtraction underflow.")).map(Self::from_gate)
    }

    /// Returns `true` the amount is positive and `false` if the amount is zero or
    /// negative.
    pub const fn is_positive(self) -> bool {
        self.0.is_positive()
    }

    /// Returns `true` if the amount is negative and `false` if the amount is zero or
    /// positive.
    pub const fn is_negative(self) -> bool {
        self.0.is_negative()
    }

    /// Returns `true` if the amount is zero and `false` if the amount is not zero.
    pub const fn is_zero(self) -> bool {
        self.0 == 0
    }

    /// Returns the amount as an i64.
    pub const fn as_i64(&self) -> i64 {
        self.0
    }
}

impl Add<Self> for Amount {
    type Output = Self;

    fn add(self, other: Self) -> Self::Output {
        match self.add(other) {
            Ok(result) => result,
            Err(err) => panic!("{}", err),
        }
    }
}

impl AddAssign<Self> for Amount {
    fn add_assign(&mut self, other: Self) {
        match self.add(other) {
            Ok(result) => *self = result,
            Err(err) => panic!("{}", err),
        }
    }
}

impl Sub<Self> for Amount {
    type Output = Self;

    fn sub(self, other: Self) -> Self::Output {
        match self.sub(other) {
            Ok(result) => result,
            Err(err) => panic!("{}", err),
        }
    }
}

impl SubAssign<Self> for Amount {
    fn sub_assign(&mut self, other: Self) {
        match self.sub(other) {
            Ok(result) => *self = result,
            Err(err) => panic!("{}", err),
        }
    }
}

impl Sum for Amount {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::ZERO, |a, b| a + b)
    }
}

impl ToBytes for Amount {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.0.write_le(&mut writer)
    }
}

impl FromBytes for Amount {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let amount: i64 = FromBytes::read_le(&mut reader)?;

        Ok(Self(amount))
    }
}

impl fmt::Display for Amount {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_from_gate(gate_value: i64, expected_amount: Amount) {
        let amount = Amount::from_gate(gate_value);
        assert_eq!(expected_amount, amount)
    }

    fn test_from_aleo(aleo_value: i64, expected_amount: Amount) {
        let amount = Amount::from_aleo(aleo_value);
        assert_eq!(expected_amount, amount)
    }

    fn test_addition(a: &i64, b: &i64, result: &i64) {
        let a = Amount::from_gate(*a);
        let b = Amount::from_gate(*b);
        let result = Amount::from_gate(*result);

        assert_eq!(result, a.add(b).unwrap());
        assert_eq!(result, a + b);
    }

    fn test_subtraction(a: &i64, b: &i64, result: &i64) {
        let a = Amount::from_gate(*a);
        let b = Amount::from_gate(*b);
        let result = Amount::from_gate(*result);

        assert_eq!(result, a.sub(b).unwrap());
        assert_eq!(result, a - b);
    }

    pub(crate) struct AmountDenominationTestCase {
        gate: i64,
        aleo: i64,
    }

    mod valid_conversions {
        use super::*;

        const TEST_AMOUNTS: [AmountDenominationTestCase; 5] = [
            AmountDenominationTestCase { gate: 0, aleo: 0 },
            AmountDenominationTestCase { gate: 1_000_000, aleo: 1 },
            AmountDenominationTestCase { gate: 1_000_000_000, aleo: 1_000 },
            AmountDenominationTestCase { gate: 1_234_567_000_000_000, aleo: 1_234_567_000 },
            AmountDenominationTestCase { gate: 1_000_000_000_000_000_000, aleo: 1_000_000_000_000 },
        ];

        #[test]
        fn test_gate_conversion() {
            TEST_AMOUNTS.iter().for_each(|amounts| test_from_gate(amounts.gate, Amount(amounts.gate)));
        }

        #[test]
        fn test_aleo_conversion() {
            TEST_AMOUNTS.iter().for_each(|amounts| test_from_aleo(amounts.aleo, Amount(amounts.gate)));
        }
    }

    mod valid_arithmetic {
        use super::*;

        const TEST_VALUES: [(i64, i64, i64); 7] = [
            (0, 0, 0),
            (1, 2, 3),
            (100000, 0, 100000),
            (123456789, 987654321, 1111111110),
            (100000000000000, 1000000000000000, 1100000000000000),
            (-100000000000000, -1000000000000000, -1100000000000000),
            (100000000000000, -100000000000000, 0),
        ];

        #[test]
        fn test_valid_addition() {
            TEST_VALUES.iter().for_each(|(a, b, c)| test_addition(a, b, c));
        }

        #[test]
        fn test_valid_subtraction() {
            TEST_VALUES.iter().for_each(|(a, b, c)| test_subtraction(c, b, a));
        }
    }

    mod test_invalid {
        use super::*;

        mod test_invalid_conversion {
            use super::*;

            const INVALID_TEST_AMOUNTS: [AmountDenominationTestCase; 4] = [
                AmountDenominationTestCase { gate: 1, aleo: 1 },
                AmountDenominationTestCase { gate: 10, aleo: 100000000 },
                AmountDenominationTestCase { gate: 1234567, aleo: 1 },
                AmountDenominationTestCase { gate: 1_000_000_000_000_000_000, aleo: 999_999_999_999 },
            ];

            #[should_panic]
            #[test]
            fn test_invalid_gate_conversion() {
                INVALID_TEST_AMOUNTS.iter().for_each(|amounts| test_from_gate(amounts.aleo, Amount(amounts.gate)));
            }

            #[should_panic]
            #[test]
            fn test_invalid_aleo_conversion() {
                INVALID_TEST_AMOUNTS.iter().for_each(|amounts| test_from_aleo(amounts.aleo, Amount(amounts.gate)));
            }
        }

        mod invalid_arithmetic {
            use super::*;

            const TEST_VALUES: [(i64, i64, i64); 5] =
                [(0, 0, 1), (1, 2, 5), (100000, 1, 100000), (123456789, 123456789, 123456789), (-1000, -1000, 2000)];

            #[should_panic]
            #[test]
            fn test_invalid_addition() {
                TEST_VALUES.iter().for_each(|(a, b, c)| test_addition(a, b, c));
            }

            #[should_panic]
            #[test]
            fn test_invalid_subtraction() {
                TEST_VALUES.iter().for_each(|(a, b, c)| test_subtraction(a, b, c));
            }

            #[test]
            fn test_invalid_addition_overflow() {
                let max_amount = Amount::from_gate(i64::MAX);
                let one_gate = Amount::ONE_GATE;

                assert!(max_amount.add(one_gate).is_err());
            }

            #[test]
            fn test_invalid_subtraction_underflow() {
                let min_amount = Amount::from_gate(i64::MIN);
                let one_gate = Amount::ONE_GATE;

                assert!(min_amount.sub(one_gate).is_err());
            }
        }
    }
}
