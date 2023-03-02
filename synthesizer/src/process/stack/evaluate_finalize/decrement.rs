// Copyright (C) 2019-2023 Aleo Systems Inc.
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

impl<N: Network> Stack<N> {
    /// Evaluates the decrement command.
    #[inline]
    pub fn evaluate_decrement<P: ProgramStorage<N>>(
        &self,
        decrement: &Decrement<N>,
        store: &ProgramStore<N, P>,
        registers: &mut FinalizeRegisters<N>,
    ) -> Result<()> {
        // Ensure the mapping exists in storage.
        if !store.contains_mapping(self.program_id(), decrement.mapping_name())? {
            bail!("Mapping '{}/{}' does not exist in storage", self.program_id(), decrement.mapping_name());
        }

        // Load the first operand as a plaintext.
        let key = registers.load_plaintext(&self, decrement.key())?;
        // Load the second operand as a literal.
        let decrement = registers.load_literal(&self, decrement.value())?;

        // Retrieve the starting value from storage as a literal.
        let start = match store.get_value(self.program_id(), &decrement.mapping, &key)? {
            Some(Value::Plaintext(Plaintext::Literal(literal, _))) => literal,
            Some(Value::Plaintext(Plaintext::Struct(..))) => bail!("Cannot 'decrement' by an 'struct'"),
            Some(Value::Record(..)) => bail!("Cannot 'decrement' by a 'record'"),
            // If the key does not exist, set the starting value to 0.
            // Infer the starting type from the decrement type.
            None => match decrement {
                Literal::Address(..) => bail!("Cannot 'decrement' by an 'address'"),
                Literal::Boolean(..) => bail!("Cannot 'decrement' by a 'boolean'"),
                Literal::Field(..) => Literal::Field(Zero::zero()),
                Literal::Group(..) => Literal::Group(Zero::zero()),
                Literal::I8(..) => Literal::I8(Zero::zero()),
                Literal::I16(..) => Literal::I16(Zero::zero()),
                Literal::I32(..) => Literal::I32(Zero::zero()),
                Literal::I64(..) => Literal::I64(Zero::zero()),
                Literal::I128(..) => Literal::I128(Zero::zero()),
                Literal::U8(..) => Literal::U8(Zero::zero()),
                Literal::U16(..) => Literal::U16(Zero::zero()),
                Literal::U32(..) => Literal::U32(Zero::zero()),
                Literal::U64(..) => Literal::U64(Zero::zero()),
                Literal::U128(..) => Literal::U128(Zero::zero()),
                Literal::Scalar(..) => Literal::Scalar(Zero::zero()),
                Literal::String(..) => bail!("Cannot 'decrement' by a 'string'"),
            },
        };

        // Decrement the value.
        let outcome = match (start, decrement) {
            (Literal::Field(a), Literal::Field(b)) => Literal::Field(a.sub(b)),
            (Literal::Group(a), Literal::Group(b)) => Literal::Group(a.sub(b)),
            (Literal::I8(a), Literal::I8(b)) => Literal::I8(a.sub(b)),
            (Literal::I16(a), Literal::I16(b)) => Literal::I16(a.sub(b)),
            (Literal::I32(a), Literal::I32(b)) => Literal::I32(a.sub(b)),
            (Literal::I64(a), Literal::I64(b)) => Literal::I64(a.sub(b)),
            (Literal::I128(a), Literal::I128(b)) => Literal::I128(a.sub(b)),
            (Literal::U8(a), Literal::U8(b)) => Literal::U8(a.sub(b)),
            (Literal::U16(a), Literal::U16(b)) => Literal::U16(a.sub(b)),
            (Literal::U32(a), Literal::U32(b)) => Literal::U32(a.sub(b)),
            (Literal::U64(a), Literal::U64(b)) => Literal::U64(a.sub(b)),
            (Literal::U128(a), Literal::U128(b)) => Literal::U128(a.sub(b)),
            (Literal::Scalar(a), Literal::Scalar(b)) => Literal::Scalar(a.sub(b)),
            (a, b) => bail!("Cannot 'decrement' '{a}' by '{b}'"),
        };

        // Construct the value.
        let value = Value::Plaintext(Plaintext::from(outcome));
        // Update the value in storage.
        store.update_key_value(self.program_id(), decrement.mapping(), key, value)?;

        Ok(())
    }
}
