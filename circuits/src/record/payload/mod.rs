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

use crate::{Boolean, Environment, Mode, traits::*};

pub struct Payload<E: Environment> {
    public: Vec<Box<dyn DataType<Boolean<E>>>>,
    private: Vec<Box<dyn DataType<Boolean<E>>>>
}

impl<E: Environment> Inject for Payload<E> {
    type Primitive = (Vec<Box<dyn DataType<Boolean<E>>>>, Vec<Box<dyn DataType<Boolean<E>>>>);

    ///
    /// Initializes a new instance of a payload.
    ///
    fn new(_: Mode, value: Self::Primitive) -> Self {
        // TODO (howardwu): Ensure the value.0 is all public, and value.1 is all private.
        Self { public: value.0, private: value.1 }
    }
}

#[cfg(test)]
mod tests {
    use crate::Affine;
    use super::*;
    use crate::{Circuit, BaseField, I64};

    #[test]
    fn test_payload() {
        let first = BaseField::<Circuit>::from_str("10field.public");
        // let second = Boolean::from_str("true.private");
        let third = I64::from_str("99i64.public");

        let candidate = Payload {
            public: vec![Box::new(first)],
            private: vec![Box::new(third)],
        };
    }
}
