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

use snarkvm_fields::Field;
use snarkvm_utilities::serialize::*;

#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct LookupTable<F: Field>(pub Vec<(F, F, F)>);

impl<F: Field> Default for LookupTable<F> {
    fn default() -> Self {
        Self(vec![])
    }
}

impl<F: Field> LookupTable<F> {
    pub fn fill(&mut self, val_1: F, val_2: F, val_3: F) {
        self.0.push((val_1, val_2, val_3))
    }
}
