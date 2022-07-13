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

// #[cfg(test)]
// use snarkvm_circuit_types::environment::assert_scope;

mod entry;
pub use entry::Entry;

mod helpers;
pub use helpers::{Balance, Owner};

mod decrypt;
mod encrypt;
mod find;
mod num_randomizers;
mod to_bits;
mod to_commitment;
mod to_fields;

use crate::{Ciphertext, Identifier, Plaintext, ProgramID, Visibility};
use snarkvm_circuit_account::ViewKey;
use snarkvm_circuit_network::Aleo;
use snarkvm_circuit_types::{environment::prelude::*, Boolean, Field, Group, Scalar, U32};

#[derive(Clone)]
pub struct Record<A: Aleo, Private: Visibility<A>> {
    /// The owner of the program record.
    owner: Owner<A, Private>,
    /// The balance of the program record.
    balance: Balance<A, Private>,
    /// The program data.
    data: IndexMap<Identifier<A>, Entry<A, Private>>,
}

#[cfg(console)]
impl<A: Aleo> Inject for Record<A, Plaintext<A>> {
    type Primitive = console::Record<A::Network, console::Plaintext<A::Network>>;

    /// Initializes a plaintext record from a primitive.
    fn new(_: Mode, record: Self::Primitive) -> Self {
        Self {
            owner: Owner::new(Mode::Private, record.owner().clone()),
            balance: Balance::new(Mode::Private, record.balance().clone()),
            data: Inject::new(Mode::Private, record.data().clone()),
        }
    }
}

#[cfg(console)]
impl<A: Aleo> Inject for Record<A, Ciphertext<A>> {
    type Primitive = console::Record<A::Network, console::Ciphertext<A::Network>>;

    /// Initializes a ciphertext record from a primitive.
    fn new(_: Mode, record: Self::Primitive) -> Self {
        Self {
            owner: Owner::new(Mode::Private, record.owner().clone()),
            balance: Balance::new(Mode::Private, record.balance().clone()),
            data: Inject::new(Mode::Private, record.data().clone()),
        }
    }
}

#[cfg(console)]
impl<A: Aleo> Record<A, Plaintext<A>> {
    /// Initializes a new record.
    pub fn from_plaintext(
        owner: Owner<A, Plaintext<A>>,
        balance: Balance<A, Plaintext<A>>,
        data: IndexMap<Identifier<A>, Entry<A, Plaintext<A>>>,
    ) -> Result<Self> {
        // Ensure the members has no duplicate names.
        ensure!(!has_duplicates(data.iter().map(|(name, ..)| name)), "A duplicate entry name was found in a record");
        // Ensure the number of interfaces is within `A::Network::MAX_DATA_ENTRIES`.
        ensure!(
            data.len() <= <A::Network as console::Network>::MAX_DATA_ENTRIES,
            "Found a record that exceeds size ({})",
            data.len()
        );
        // Return the record.
        Ok(Self { owner, balance, data })
    }
}

#[cfg(console)]
impl<A: Aleo> Record<A, Ciphertext<A>> {
    /// Initializes a new record.
    pub fn from_ciphertext(
        owner: Owner<A, Ciphertext<A>>,
        balance: Balance<A, Ciphertext<A>>,
        data: IndexMap<Identifier<A>, Entry<A, Ciphertext<A>>>,
    ) -> Result<Self> {
        // Ensure the members has no duplicate names.
        ensure!(!has_duplicates(data.iter().map(|(name, ..)| name)), "A duplicate entry name was found in a record");
        // Ensure the number of interfaces is within `A::Network::MAX_DATA_ENTRIES`.
        ensure!(
            data.len() <= <A::Network as console::Network>::MAX_DATA_ENTRIES,
            "Found a record that exceeds size ({})",
            data.len()
        );
        // Return the record.
        Ok(Self { owner, balance, data })
    }
}

impl<A: Aleo, Private: Visibility<A>> Record<A, Private> {
    /// Returns the owner of the program record.
    pub const fn owner(&self) -> &Owner<A, Private> {
        &self.owner
    }

    /// Returns the balance of the program record.
    pub const fn balance(&self) -> &Balance<A, Private> {
        &self.balance
    }

    /// Returns the program data.
    pub const fn data(&self) -> &IndexMap<Identifier<A>, Entry<A, Private>> {
        &self.data
    }
}

#[cfg(console)]
impl<A: Aleo> Eject for Record<A, Plaintext<A>> {
    type Primitive = console::Record<A::Network, console::Plaintext<A::Network>>;

    /// Ejects the mode of the record.
    fn eject_mode(&self) -> Mode {
        let owner = match &self.owner {
            Owner::Public(owner) => match owner.eject_mode() == Mode::Public {
                true => Mode::Public,
                false => A::halt("Record::<Plaintext>::eject_mode: public owner is not public."),
            },
            Owner::Private(plaintext) => match plaintext.eject_mode() == Mode::Private {
                true => Mode::Private,
                false => A::halt("Record::<Plaintext>::eject_mode: private owner is not private."),
            },
        };

        let balance = match &self.balance {
            Balance::Public(balance) => match balance.eject_mode() == Mode::Public {
                true => Mode::Public,
                false => A::halt("Record::<Plaintext>::eject_mode: public balance is not public."),
            },
            Balance::Private(plaintext) => match plaintext.eject_mode() == Mode::Private {
                true => Mode::Private,
                false => A::halt("Record::<Plaintext>::eject_mode: private balance is not private."),
            },
        };

        let data = self.data.iter().map(|(_, entry)| entry.eject_mode()).collect::<Vec<_>>().eject_mode();

        Mode::combine(owner, [balance, data])
    }

    /// Ejects the record.
    fn eject_value(&self) -> Self::Primitive {
        let owner = match &self.owner {
            Owner::Public(owner) => console::Owner::Public(owner.eject_value()),
            Owner::Private(plaintext) => console::Owner::Private(plaintext.eject_value()),
        };

        let balance = match &self.balance {
            Balance::Public(balance) => console::Balance::Public(balance.eject_value()),
            Balance::Private(plaintext) => console::Balance::Private(plaintext.eject_value()),
        };

        match Self::Primitive::from_plaintext(
            owner,
            balance,
            self.data.iter().map(|(identifier, entry)| (identifier, entry).eject_value()).collect::<IndexMap<_, _>>(),
        ) {
            Ok(record) => record,
            Err(error) => A::halt(format!("Record::<Plaintext>::eject_value: {}", error)),
        }
    }
}

#[cfg(console)]
impl<A: Aleo> Eject for Record<A, Ciphertext<A>> {
    type Primitive = console::Record<A::Network, console::Ciphertext<A::Network>>;

    /// Ejects the mode of the record.
    fn eject_mode(&self) -> Mode {
        let owner = match &self.owner {
            Owner::Public(owner) => match owner.eject_mode() == Mode::Public {
                true => Mode::Public,
                false => A::halt("Record::<Ciphertext>::eject_mode: public owner is not public."),
            },
            Owner::Private(plaintext) => match plaintext.eject_mode() == Mode::Private {
                true => Mode::Private,
                false => A::halt("Record::<Ciphertext>::eject_mode: private owner is not private."),
            },
        };

        let balance = match &self.balance {
            Balance::Public(balance) => match balance.eject_mode() == Mode::Public {
                true => Mode::Public,
                false => A::halt("Record::<Ciphertext>::eject_mode: public balance is not public."),
            },
            Balance::Private(plaintext) => match plaintext.eject_mode() == Mode::Private {
                true => Mode::Private,
                false => A::halt("Record::<Ciphertext>::eject_mode: private balance is not private."),
            },
        };

        let data = self.data.iter().map(|(_, entry)| entry.eject_mode()).collect::<Vec<_>>().eject_mode();

        Mode::combine(owner, [balance, data])
    }

    /// Ejects the record.
    fn eject_value(&self) -> Self::Primitive {
        let owner = match &self.owner {
            Owner::Public(owner) => console::Owner::Public(owner.eject_value()),
            Owner::Private(plaintext) => console::Owner::Private(plaintext.eject_value()),
        };

        let balance = match &self.balance {
            Balance::Public(balance) => console::Balance::Public(balance.eject_value()),
            Balance::Private(plaintext) => console::Balance::Private(plaintext.eject_value()),
        };

        match Self::Primitive::from_ciphertext(
            owner,
            balance,
            self.data.iter().map(|(identifier, entry)| (identifier, entry).eject_value()).collect::<IndexMap<_, _>>(),
        ) {
            Ok(record) => record,
            Err(error) => A::halt(format!("Record::<Ciphertext>::eject_value: {}", error)),
        }
    }
}

#[cfg(console)]
impl<A: Aleo, Private: Visibility<A>> TypeName for Record<A, Private> {
    fn type_name() -> &'static str {
        "record"
    }
}
