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

impl<A: Aleo> ToFields for Request<A> {
    type Field = Field<A>;

    /// Returns this request as a list of field elements.
    fn to_fields(&self) -> Vec<Self::Field> {
        // Initialize a vector for the list of field elements.
        let mut fields = Vec::with_capacity(4 + self.inputs.len());
        fields.push(self.caller.to_field());
        fields.push(self.network_id.to_field());
        fields.extend(self.program_id.to_fields());
        fields.push(self.function_name.to_field());
        fields.extend(self.inputs.iter().map(|input| input.to_fields()).flatten());

        // Ensure the number of field elements does not exceed the maximum allowed size.
        match fields.len() <= A::MAX_DATA_SIZE_IN_FIELDS as usize {
            true => fields,
            false => A::halt("Request exceeds maximum allowed size"),
        }
    }
}
