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

/// A helper macro to downcast a `$variable` to `$object<$network>`.
#[macro_export]
macro_rules! cast_ref {
    // Example: cast_ref!((foo.bar()) as Bar<Testnet3>)
    (($variable:expr) as $object:ident<$($traits:path),+>) => {{
        (&$variable as &dyn std::any::Any)
            .downcast_ref::<$object<$($traits),+>>()
            .ok_or_else(|| anyhow!("Failed to downcast {}", stringify!($variable)))?
    }};
    // Example: cast_ref!(bar as Bar<Testnet3>)
    ($variable:ident as $object:ident<$($traits:path),+>) => {{
        (&$variable as &dyn std::any::Any)
            .downcast_ref::<$object<$($traits),+>>()
            .ok_or_else(|| anyhow!("Failed to downcast {}", stringify!($variable)))?
    }};
    // Example: cast_ref!(&bar as Bar<Testnet3>)
    (&$variable:ident as $object:ident<$($traits:path),+>) => {{
        ($variable as &dyn std::any::Any)
            .downcast_ref::<$object<$($traits),+>>()
            .ok_or_else(|| anyhow!("Failed to downcast {}", stringify!($variable)))?
    }};
}

/// A helper macro to dedup the `Network` trait and `Aleo` trait and process its given logic.
#[macro_export]
macro_rules! process {
    // Example: process!(self, logic)
    ($self:ident, $logic:ident) => {{
        // Process the logic.
        match N::ID {
            console::network::Testnet3::ID => {
                // Cast the process.
                let process = (&$self.process as &dyn std::any::Any)
                    .downcast_ref::<Arc<RwLock<Process<console::network::Testnet3>>>>()
                    .ok_or_else(|| anyhow!("Failed to downcast {}", stringify!($self.process)))
                    .unwrap();

                $logic!(process.read(), console::network::Testnet3, circuit::AleoV0)
            }
            _ => Err(anyhow!("Unsupported VM configuration for network: {}", N::ID)),
        }
    }};
}
