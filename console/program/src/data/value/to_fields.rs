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

use super::*;

impl<N: Network> ToFields for Value<N> {
    type Field = Field<N>;

    /// Returns the stack value as a list of fields.
    #[inline]
    fn to_fields(&self) -> Result<Vec<Self::Field>> {
        // // TODO (howardwu): Implement `Literal::to_fields()` to replace this closure.
        // // (Optional) Closure for converting a list of literals into a list of field elements.
        // //
        // // If the list is comprised of `Address`, `Field`, `Group`, and/or `Scalar`, then the closure
        // // will return the underlying field elements (instead of packing the literals from bits).
        // // Otherwise, the list is converted into bits, and then packed into field elements.
        // let to_field_elements = |input: &[Literal<_>]| {
        //     // Determine whether the input is comprised of field-friendly literals.
        //     match input.iter().all(|literal| {
        //         matches!(literal, Literal::Address(_) | Literal::Field(_) | Literal::Group(_) | Literal::Scalar(_))
        //     }) {
        //         // Case 1 - Map each literal directly to its field representation.
        //         true => input
        //             .iter()
        //             .map(|literal| match literal {
        //                 Literal::Address(address) => address.to_field(),
        //                 Literal::Field(field) => field.clone(),
        //                 Literal::Group(group) => group.to_x_coordinate(),
        //                 Literal::Scalar(scalar) => scalar.to_field(),
        //                 _ => P::halt("Unreachable literal variant detected during hashing."),
        //             })
        //             .collect::<Vec<_>>(),
        //         // Case 2 - Convert the literals to bits, and then pack them into field elements.
        //         false => input
        //             .to_bits_le()
        //             .chunks(<P::Environment as Environment>::BaseField::size_in_data_bits())
        //             .map(FromBits::from_bits_le)
        //             .collect::<Vec<_>>(),
        //     }
        // };

        match self {
            Self::Plaintext(plaintext) => plaintext.to_fields(),
            Self::Record(record) => record.to_fields(),
        }
    }
}
