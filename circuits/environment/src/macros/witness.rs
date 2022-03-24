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

/// The `witness!` macro is a closure that takes in a list of circuits,
/// eject the value of each circuit, and uses it in the subsequent code block.
/// In addition,
///
/// This macro requires `Inject` to be implemented on the return type,
/// and `Eject` to be implemented on all inputs.
#[macro_export]
macro_rules! witness {
    (| $($circuit:ident),* | $block:block) => {
        {
            // Determine if all given circuits are constant.
            let is_constant = { $( $circuit.is_constant() & )* true };

            // Determine the witness mode.
            let mode = match is_constant {
                true => Mode::Constant,
                false => Mode::Private
            };

            // Reassign each circuit to its primitive type.
            $( let $circuit = $circuit.eject_value(); )*

            // Execute the code block, returning the primitive to be injected.
            Inject::new(mode, $block)
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::*;

    /// A dummy struct for testing `witness!`.
    pub struct Foo(Mode, u8);

    impl Inject for Foo {
        type Primitive = u8;

        fn new(mode: Mode, value: Self::Primitive) -> Self {
            Self(mode, value)
        }
    }

    impl Eject for Foo {
        type Primitive = u8;

        fn eject_mode(&self) -> Mode {
            self.0
        }

        fn eject_value(&self) -> Self::Primitive {
            self.1
        }
    }

    #[test]
    fn test_witness_constant() {
        let x = Foo::new(Mode::Constant, 3);
        let y = Foo::new(Mode::Constant, 5);
        let z: Foo = witness!(|x, y| { x + y });
        assert_eq!(Mode::Constant, z.eject_mode());
        assert_eq!(8, z.eject_value());
    }

    #[test]
    fn test_witness_private() {
        let x = Foo::new(Mode::Constant, 3);
        let y = Foo::new(Mode::Private, 5);
        let z: Foo = witness!(|x, y| { x + y });
        assert_eq!(Mode::Private, z.eject_mode());
        assert_eq!(8, z.eject_value());
    }
}
