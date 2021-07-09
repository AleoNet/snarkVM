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

use snarkvm_utilities::{FromBytes, ToBytes};

use std::{
    fmt,
    io::{Read, Result as IoResult, Write},
};

/// Represents the network the node operating on.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Network {
    Mainnet,
    Testnet1,
    Testnet2,
    Custom(u8),
}

impl Network {
    /// Returns the network from a given network ID.
    pub const fn from_id(network_id: u8) -> Self {
        match network_id {
            0 => Network::Mainnet,
            1 => Network::Testnet1,
            2 => Network::Testnet2,
            id => Network::Custom(id),
        }
    }

    /// Returns the ID of the network.
    pub const fn id(&self) -> u8 {
        match self {
            Network::Mainnet => 0,
            Network::Testnet1 => 1,
            Network::Testnet2 => 2,
            Network::Custom(id) => *id,
        }
    }
}

impl ToBytes for Network {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.id().write_le(&mut writer)
    }
}

impl FromBytes for Network {
    #[inline]
    fn read<R: Read>(mut reader: R) -> IoResult<Self> {
        let network_id: u8 = FromBytes::read(&mut reader)?;
        Ok(Self::from_id(network_id))
    }
}

impl fmt::Display for Network {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.id())
    }
}
