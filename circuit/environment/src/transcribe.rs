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
