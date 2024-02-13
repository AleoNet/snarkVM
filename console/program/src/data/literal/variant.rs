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

impl<N: Network> Literal<N> {
    /// Returns the variant of the literal.
    pub fn variant(&self) -> u8 {
        match self {
            Self::Address(..) => 0,
            Self::Boolean(..) => 1,
            Self::Data(..) => 2,
            Self::Field(..) => 3,
            Self::Group(..) => 4,
            Self::I8(..) => 5,
            Self::I16(..) => 6,
            Self::I32(..) => 7,
            Self::I64(..) => 8,
            Self::I128(..) => 9,
            Self::U8(..) => 10,
            Self::U16(..) => 11,
            Self::U32(..) => 12,
            Self::U64(..) => 13,
            Self::U128(..) => 14,
            Self::Scalar(..) => 15,
            Self::Signature(..) => 16,
            Self::String(..) => 17,
        }
    }
}
