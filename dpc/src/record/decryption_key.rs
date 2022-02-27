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

use crate::{Network, ViewKey};
use std::fmt;

#[derive(Clone, PartialEq, Eq)]
pub enum DecryptionKey<N: Network> {
    AccountViewKey(ViewKey<N>),
    RecordViewKey(N::RecordViewKey),
}

impl<N: Network> DecryptionKey<N> {
    pub fn from_record_view_key(record_view_key: &N::RecordViewKey) -> Self {
        Self::RecordViewKey(record_view_key.clone())
    }
}

impl<N: Network> From<ViewKey<N>> for DecryptionKey<N> {
    fn from(account_view_key: ViewKey<N>) -> Self {
        Self::AccountViewKey(account_view_key)
    }
}

impl<N: Network> From<&ViewKey<N>> for DecryptionKey<N> {
    fn from(account_view_key: &ViewKey<N>) -> Self {
        Self::from(account_view_key.clone())
    }
}

impl<N: Network> fmt::Display for DecryptionKey<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            DecryptionKey::AccountViewKey(account_view_key) => write!(f, "{}", account_view_key),
            DecryptionKey::RecordViewKey(record_view_key) => write!(f, "{}", record_view_key),
        }
    }
}

impl<N: Network> fmt::Debug for DecryptionKey<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            DecryptionKey::AccountViewKey(account_view_key) => {
                write!(f, "DecryptionKey {{ account_view_key: {:?} }}", account_view_key)
            }
            DecryptionKey::RecordViewKey(record_view_key) => {
                write!(f, "DecryptionKey {{ record_view_key: {:?} }}", record_view_key)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testnet2::Testnet2;

    use crate::{Account, AleoAmount, Transaction};
    use rand::thread_rng;

    #[test]
    fn test_account_view_key_into() {
        let rng = &mut thread_rng();
        let account = Account::<Testnet2>::new(rng);

        // Conversion should not fail
        let _decryption_key: DecryptionKey<Testnet2> = account.view_key().into();
    }

    #[test]
    fn test_record_view_key_into() {
        let rng = &mut thread_rng();
        let account = Account::<Testnet2>::new(rng);

        // Craft a transaction with 1 coinbase record.
        let (transaction, _expected_record) =
            Transaction::new_coinbase(account.address(), AleoAmount(1234), true, rng).unwrap();

        let public_records = transaction.to_records().collect::<Vec<_>>();
        let record = public_records.first().unwrap();

        // Conversion should not fail
        // let decryption_key: DecryptionKey<Testnet2> = record.record_view_key().into();

        // Workaround
        let _decryption_key = DecryptionKey::<Testnet2>::from_record_view_key(record.record_view_key());
    }
}
