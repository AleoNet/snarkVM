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

/// This is an error that could occur during circuit construction contexts.
#[derive(Debug, Error)]
pub enum EnvironmentError {
    /// During synthesis, we attempted to lookup a variable without a lookup table
    /// being present in the constraint system.
    #[error("Lookup table missing")]
    LookupTableMissing,
    /// During synthesis, we attempted to lookup a variable without this variable
    /// being present in the lookup table.
    #[error("Lookup value missing")]
    LookupValueMissing,
}
