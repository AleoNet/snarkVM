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

impl<E: Environment> Verify for TableExampleVerifier<E> {
    type Input = Field<E>;

    fn verify(&self, input: &[Self::Input]) -> Result<bool> {
        let input = input.to_vec();

        let key_0 = input[0];
        let key_1 = input[1];
        let value = input[2];
        let table_index = 0;

        let result = *self.tables[table_index].lookup(&[key_0, key_1]).unwrap().2 == value;

        Ok(result)
    }
}
