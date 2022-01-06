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

use crate::{Network, ViewKey};

#[derive(Derivative)]
#[derivative(
    Clone(bound = "N: Network"),
    PartialEq(bound = "N: Network"),
    Eq(bound = "N: Network")
)]
pub enum DecryptionKey<N: Network> {
    AccountViewKey(ViewKey<N>),
    RecordViewKey(N::RecordViewKey),
}

impl<N: Network> From<&ViewKey<N>> for DecryptionKey<N> {
    fn from(account_view_key: &ViewKey<N>) -> Self {
        Self::AccountViewKey(account_view_key.clone())
    }
}

impl<N: Network> From<&N::RecordViewKey> for DecryptionKey<N> {
    fn from(record_view_key: &N::RecordViewKey) -> Self {
        Self::RecordViewKey(record_view_key.clone())
    }
}
