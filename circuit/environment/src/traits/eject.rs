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

use crate::Mode;

/// Operations to eject from a circuit environment into primitive form.
pub trait Eject {
    type Primitive;

    ///
    /// Ejects the mode and primitive value of the circuit type.
    ///
    fn eject(&self) -> (Mode, Self::Primitive) {
        (self.eject_mode(), self.eject_value())
    }

    ///
    /// Ejects the mode of the circuit type.
    ///
    fn eject_mode(&self) -> Mode;

    ///
    /// Ejects the circuit type as a primitive value.
    ///
    fn eject_value(&self) -> Self::Primitive;

    ///
    /// Returns `true` if the circuit is a constant.
    ///
    fn is_constant(&self) -> bool {
        self.eject_mode().is_constant()
    }

    ///
    /// Returns `true` if the circuit is a public.
    ///
    fn is_public(&self) -> bool {
        self.eject_mode().is_public()
    }

    ///
    /// Returns `true` if the circuit is a private.
    ///
    fn is_private(&self) -> bool {
        self.eject_mode().is_private()
    }
}

/********************/
/****** Arrays ******/
/********************/

impl Eject for Vec<Mode> {
    type Primitive = Vec<Mode>;

    /// A helper method to deduce the mode from a list of `Eject` circuits.
    #[inline]
    fn eject_mode(&self) -> Mode {
        // TODO (howardwu): Determine if a default mode of `constant` is appropriate.
        // Retrieve the mode of the first circuit.
        match self.get(0) {
            Some(first) => Mode::combine(*first, self.iter().copied().skip(1)),
            // None => Mode::Constant,
            None => panic!("Attempted to eject the mode on an empty circuit"),
        }
    }

    /// Ejects the value from each circuit.
    #[inline]
    fn eject_value(&self) -> Self::Primitive {
        self.clone()
    }
}

impl<C: Eject<Primitive = P>, P> Eject for Vec<C> {
    type Primitive = Vec<P>;

    /// A helper method to deduce the mode from a list of `Eject` circuits.
    #[inline]
    fn eject_mode(&self) -> Mode {
        self.as_slice().eject_mode()
    }

    /// Ejects the value from each circuit.
    #[inline]
    fn eject_value(&self) -> Self::Primitive {
        self.as_slice().eject_value()
    }
}

impl<C: Eject<Primitive = P>, P, const N: usize> Eject for [C; N] {
    type Primitive = Vec<P>;

    /// A helper method to deduce the mode from a list of `Eject` circuits.
    #[inline]
    fn eject_mode(&self) -> Mode {
        self.as_slice().eject_mode()
    }

    /// Ejects the value from each circuit.
    #[inline]
    fn eject_value(&self) -> Self::Primitive {
        self.as_slice().eject_value()
    }
}

impl<C: Eject<Primitive = P>, P> Eject for &[C] {
    type Primitive = Vec<P>;

    /// A helper method to deduce the mode from a list of `Eject` circuits.
    #[inline]
    fn eject_mode(&self) -> Mode {
        // TODO (howardwu): Determine if a default mode of `constant` is appropriate.
        // Retrieve the mode of the first circuit.
        match self.get(0) {
            Some(first) => Mode::combine(first.eject_mode(), self.iter().skip(1).map(Eject::eject_mode)),
            None => Mode::Constant,
            // None => panic!("Attempted to eject the mode on an empty circuit"),
        }
    }

    /// Ejects the value from each circuit.
    #[inline]
    fn eject_value(&self) -> Self::Primitive {
        self.iter().map(Eject::eject_value).collect()
    }
}

/********************/
/****** Tuples ******/
/********************/

/// A helper macro to implement `Eject` for a tuple of `Eject` circuits.
macro_rules! eject_tuple {
    (($t0:ident, $i0:expr), $(($ty:ident, $idx:tt)),*) => {
        impl<'a, $t0: Eject, $($ty: Eject),*> Eject for (&'a $t0, $(&'a $ty),*) {
            type Primitive = ($t0::Primitive, $( $ty::Primitive ),*);

            /// A helper method to deduce the mode from a tuple of `Eject` circuits.
            #[inline]
            fn eject_mode(&self) -> Mode {
                Mode::combine(self.0.eject_mode(), [ $(self.$idx.eject_mode()),* ])
            }

            /// Ejects the value from each circuit.
            #[inline]
            fn eject_value(&self) -> Self::Primitive {
                (self.0.eject_value(), $(self.$idx.eject_value()),*)
            }
        }

        impl<'a, $t0: Eject, $($ty: Eject),*> Eject for &'a ($t0, $($ty),*) {
            type Primitive = ($t0::Primitive, $( $ty::Primitive ),*);

            /// A helper method to deduce the mode from a tuple of `Eject` circuits.
            #[inline]
            fn eject_mode(&self) -> Mode {
                Mode::combine(self.0.eject_mode(), [ $(self.$idx.eject_mode()),* ])
            }

            /// Ejects the value from each circuit.
            #[inline]
            fn eject_value(&self) -> Self::Primitive {
                (self.0.eject_value(), $(self.$idx.eject_value()),*)
            }
        }
    }
}

eject_tuple!((C0, 0),);
eject_tuple!((C0, 0), (C1, 1));
eject_tuple!((C0, 0), (C1, 1), (C2, 2));
eject_tuple!((C0, 0), (C1, 1), (C2, 2), (C3, 3));
eject_tuple!((C0, 0), (C1, 1), (C2, 2), (C3, 3), (C4, 4));
eject_tuple!((C0, 0), (C1, 1), (C2, 2), (C3, 3), (C4, 4), (C5, 5));
eject_tuple!((C0, 0), (C1, 1), (C2, 2), (C3, 3), (C4, 4), (C5, 5), (C6, 6));
eject_tuple!((C0, 0), (C1, 1), (C2, 2), (C3, 3), (C4, 4), (C5, 5), (C6, 6), (C7, 7));
eject_tuple!((C0, 0), (C1, 1), (C2, 2), (C3, 3), (C4, 4), (C5, 5), (C6, 6), (C7, 7), (C8, 8));
eject_tuple!((C0, 0), (C1, 1), (C2, 2), (C3, 3), (C4, 4), (C5, 5), (C6, 6), (C7, 7), (C8, 8), (C9, 9));
eject_tuple!((C0, 0), (C1, 1), (C2, 2), (C3, 3), (C4, 4), (C5, 5), (C6, 6), (C7, 7), (C8, 8), (C9, 9), (C10, 10));
