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
/****** Helper ******/
/********************/

/// A helper method to deduce the mode from a list of `Eject` circuits.
#[inline]
fn eject_mode(start_mode: Mode, modes: &[Mode]) -> Mode {
    let mut current_mode = start_mode;
    for next_mode in modes {
        // Check if the current mode matches the next mode.
        if !current_mode.is_private() && current_mode != *next_mode {
            // If the current mode is not Mode::Private, and they do not match:
            //  - If the next mode is Mode::Private, then set the current mode to Mode::Private.
            //  - If the next mode is Mode::Public, then set the current mode to Mode::Private.
            match (current_mode, next_mode) {
                (Mode::Constant, Mode::Public) | (Mode::Constant, Mode::Private) | (Mode::Public, Mode::Private) => {
                    current_mode = *next_mode
                }
                (_, _) => (), // Do nothing.
            }
        }
    }
    current_mode
}

/********************/
/****** Arrays ******/
/********************/

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
            Some(first) => {
                eject_mode(first.eject_mode(), &self.iter().skip(1).map(Eject::eject_mode).collect::<Vec<_>>())
            }
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

impl<'a, C0: Eject, C1: Eject> Eject for (&'a C0, &'a C1) {
    type Primitive = (C0::Primitive, C1::Primitive);

    /// A helper method to deduce the mode from a tuple of `Eject` circuits.
    #[inline]
    fn eject_mode(&self) -> Mode {
        eject_mode(self.0.eject_mode(), &[self.1.eject_mode()])
    }

    /// Ejects the value from each circuit.
    #[inline]
    fn eject_value(&self) -> Self::Primitive {
        (self.0.eject_value(), self.1.eject_value())
    }
}

impl<'a, C0: Eject, C1: Eject, C2: Eject> Eject for (&'a C0, &'a C1, &'a C2) {
    type Primitive = (C0::Primitive, C1::Primitive, C2::Primitive);

    /// A helper method to deduce the mode from a tuple of `Eject` circuits.
    #[inline]
    fn eject_mode(&self) -> Mode {
        eject_mode(self.0.eject_mode(), &[self.1.eject_mode(), self.2.eject_mode()])
    }

    /// Ejects the value from each circuit.
    #[inline]
    fn eject_value(&self) -> Self::Primitive {
        (self.0.eject_value(), self.1.eject_value(), self.2.eject_value())
    }
}

impl<'a, C0: Eject, C1: Eject, C2: Eject, C3: Eject> Eject for (&'a C0, &'a C1, &'a C2, &'a C3) {
    type Primitive = (C0::Primitive, C1::Primitive, C2::Primitive, C3::Primitive);

    /// A helper method to deduce the mode from a tuple of `Eject` circuits.
    #[inline]
    fn eject_mode(&self) -> Mode {
        eject_mode(self.0.eject_mode(), &[self.1.eject_mode(), self.2.eject_mode(), self.3.eject_mode()])
    }

    /// Ejects the value from each circuit.
    #[inline]
    fn eject_value(&self) -> Self::Primitive {
        (self.0.eject_value(), self.1.eject_value(), self.2.eject_value(), self.3.eject_value())
    }
}
