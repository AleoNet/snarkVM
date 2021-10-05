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

macro_rules! to_bits_le_impl {
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
