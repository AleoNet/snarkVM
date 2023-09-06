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

/// A trait for objects that produce a transcript of their behavior.
pub trait Transcribe {
    type Transcript;

    /// Creates and enters a scope of the transcript.
    fn push() {}

    /// Exits the current scope of the transcript.
    fn pop() {}

    /// Logs a message into the current scope of the transcript.
    fn log(_message: String) {}

    /// Clears and returns the accumulated transcript.
    fn clear() -> Self::Transcript;
}
