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

use crate::{Annotation, Locator, Register};
use snarkvm_circuits_types::prelude::*;

use core::{cmp::Ordering, fmt};

/// The input statement defines an input argument to a function.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Input<E: Environment> {
    /// The input register.
    register: Register<E>,
    /// The input annotation.
    annotation: Annotation<E>,
}

impl<E: Environment> Input<E> {
    /// Initializes a new input.
    ///
    /// # Errors
    /// This function will halt if the given register is a register member.
    #[inline]
    pub fn new(register: Register<E>, annotation: Annotation<E>) -> Self {
        // Ensure the register is not a register member.
        if let Register::Member(..) = register {
            E::halt("Input register cannot be a register member")
        }
        Self { register, annotation }
    }

    /// Returns the input register.
    #[inline]
    pub fn register(&self) -> &Register<E> {
        &self.register
    }

    /// Returns the input register locator.
    #[inline]
    pub fn locator(&self) -> &Locator {
        self.register.locator()
    }

    /// Returns the input annotation.
    #[inline]
    pub fn annotation(&self) -> &Annotation<E> {
        &self.annotation
    }

    /// Returns `true` if the input is a literal.
    /// Returns `false` if the input is a composite or record.
    pub fn is_literal(&self) -> bool {
        self.annotation.is_literal()
    }

    /// Returns `true` if the input is a composite.
    /// Returns `false` if the input is a literal or record.
    pub fn is_composite(&self) -> bool {
        self.annotation.is_composite()
    }

    /// Returns `true` if the input is a record.
    /// Returns `false` if the input is a literal or composite.
    pub fn is_record(&self) -> bool {
        self.annotation.is_record()
    }
}

impl<E: Environment> TypeName for Input<E> {
    /// Returns the type name as a string.
    #[inline]
    fn type_name() -> &'static str {
        "input"
    }
}

impl<E: Environment> Parser for Input<E> {
    type Environment = E;

    /// Parses a string into an input statement.
    /// The input statement is of the form `input {register} {annotation}`.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the input keyword from the string.
        let (string, _) = tag(Self::type_name())(string)?;
        // Parse the space from the string.
        let (string, _) = tag(" ")(string)?;
        // Parse the register from the string.
        let (string, register) = Register::parse(string)?;
        // Parse the space from the string.
        let (string, _) = tag(" ")(string)?;
        // Parse the annotation from the string.
        let (string, annotation) = Annotation::parse(string)?;
        // Parse the semicolon from the string.
        let (string, _) = tag(";")(string)?;
        // Return the input statement.
        Ok((string, Self::new(register, annotation)))
    }
}

impl<E: Environment> fmt::Display for Input<E> {
    /// Prints the input statement as a string.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{type_} {register} {annotation};",
            type_ = Self::type_name(),
            register = self.register,
            annotation = self.annotation
        )
    }
}

impl<E: Environment> Ord for Input<E> {
    /// Ordering is determined by the register (the annotation is ignored).
    fn cmp(&self, other: &Self) -> Ordering {
        self.register().cmp(other.register())
    }
}

impl<E: Environment> PartialOrd for Input<E> {
    /// Ordering is determined by the register (the annotation is ignored).
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Identifier, Type};
    use snarkvm_circuits_types::environment::Circuit;

    type E = Circuit;

    #[test]
    fn test_input_type_name() {
        assert_eq!(Input::<E>::type_name(), "input");
    }

    #[test]
    fn test_input_parse() {
        // Literal
        let input = Input::<E>::parse("input r0 field.private;").unwrap().1;
        assert_eq!(input.register(), &Register::<E>::Locator(0));
        assert_eq!(input.annotation(), &Annotation::<E>::Literal(Type::Field(Mode::Private)));

        // Composite
        let input = Input::<E>::parse("input r1 signature;").unwrap().1;
        assert_eq!(input.register(), &Register::<E>::Locator(1));
        assert_eq!(input.annotation(), &Annotation::<E>::Composite(Identifier::new("signature")));

        // Record
        let input = Input::<E>::parse("input r2 record;").unwrap().1;
        assert_eq!(input.register(), &Register::<E>::Locator(2));
        assert_eq!(input.annotation(), &Annotation::<E>::Record);
    }

    #[test]
    fn test_input_display() {
        // Literal
        let input = Input::<E>::new(Register::<E>::Locator(0), Annotation::<E>::Literal(Type::Field(Mode::Private)));
        assert_eq!("input r0 field.private;", input.to_string());

        // Composite
        let input =
            Input::<E>::new(Register::<E>::Locator(1), Annotation::<E>::Composite(Identifier::new("signature")));
        assert_eq!("input r1 signature;", input.to_string());

        // Record
        let input = Input::<E>::new(Register::<E>::Locator(2), Annotation::<E>::Record);
        assert_eq!("input r2 record;", input.to_string());
    }

    #[test]
    fn test_input_locator() {
        // Literal
        let input = Input::<E>::new(Register::<E>::Locator(0), Annotation::<E>::Literal(Type::Field(Mode::Private)));
        assert_eq!(input.locator(), &0);

        // Composite
        let input =
            Input::<E>::new(Register::<E>::Locator(1), Annotation::<E>::Composite(Identifier::new("signature")));
        assert_eq!(input.locator(), &1);

        // Record
        let input = Input::<E>::new(Register::<E>::Locator(2), Annotation::<E>::Record);
        assert_eq!(input.locator(), &2);
    }

    #[test]
    fn test_input_is_literal() {
        // Literal
        let input = Input::<E>::new(Register::<E>::Locator(0), Annotation::<E>::Literal(Type::Field(Mode::Private)));
        assert!(input.is_literal());

        // Composite
        let input =
            Input::<E>::new(Register::<E>::Locator(1), Annotation::<E>::Composite(Identifier::new("signature")));
        assert!(!input.is_literal());

        // Record
        let input = Input::<E>::new(Register::<E>::Locator(2), Annotation::<E>::Record);
        assert!(!input.is_literal());
    }

    #[test]
    fn test_input_is_composite() {
        // Literal
        let input = Input::<E>::new(Register::<E>::Locator(0), Annotation::<E>::Literal(Type::Field(Mode::Private)));
        assert!(!input.is_composite());

        // Composite
        let input =
            Input::<E>::new(Register::<E>::Locator(1), Annotation::<E>::Composite(Identifier::new("signature")));
        assert!(input.is_composite());

        // Record
        let input = Input::<E>::new(Register::<E>::Locator(2), Annotation::<E>::Record);
        assert!(!input.is_composite());
    }

    #[test]
    fn test_input_is_record() {
        // Literal
        let input = Input::<E>::new(Register::<E>::Locator(0), Annotation::<E>::Literal(Type::Field(Mode::Private)));
        assert!(!input.is_record());

        // Composite
        let input =
            Input::<E>::new(Register::<E>::Locator(1), Annotation::<E>::Composite(Identifier::new("signature")));
        assert!(!input.is_record());

        // Record
        let input = Input::<E>::new(Register::<E>::Locator(2), Annotation::<E>::Record);
        assert!(input.is_record());
    }

    #[test]
    fn test_input_partial_ord() {
        let input1 = Input::<E>::new(Register::<E>::Locator(0), Annotation::<E>::Literal(Type::Field(Mode::Private)));
        let input2 = Input::<E>::new(Register::<E>::Locator(1), Annotation::<E>::Literal(Type::Field(Mode::Private)));

        let input3 =
            Input::<E>::new(Register::<E>::Locator(0), Annotation::<E>::Composite(Identifier::new("signature")));
        let input4 =
            Input::<E>::new(Register::<E>::Locator(1), Annotation::<E>::Composite(Identifier::new("signature")));

        let input5 = Input::<E>::new(Register::<E>::Locator(0), Annotation::<E>::Record);
        let input6 = Input::<E>::new(Register::<E>::Locator(1), Annotation::<E>::Record);

        assert_eq!(input1.partial_cmp(&input1), Some(Ordering::Equal));
        assert_eq!(input1.partial_cmp(&input2), Some(Ordering::Less));
        assert_eq!(input1.partial_cmp(&input3), Some(Ordering::Equal));
        assert_eq!(input1.partial_cmp(&input4), Some(Ordering::Less));
        assert_eq!(input1.partial_cmp(&input5), Some(Ordering::Equal));
        assert_eq!(input1.partial_cmp(&input6), Some(Ordering::Less));

        assert_eq!(input2.partial_cmp(&input1), Some(Ordering::Greater));
        assert_eq!(input2.partial_cmp(&input2), Some(Ordering::Equal));
        assert_eq!(input2.partial_cmp(&input3), Some(Ordering::Greater));
        assert_eq!(input2.partial_cmp(&input4), Some(Ordering::Equal));
        assert_eq!(input2.partial_cmp(&input5), Some(Ordering::Greater));
        assert_eq!(input2.partial_cmp(&input6), Some(Ordering::Equal));

        assert_eq!(input3.partial_cmp(&input1), Some(Ordering::Equal));
        assert_eq!(input3.partial_cmp(&input2), Some(Ordering::Less));
        assert_eq!(input3.partial_cmp(&input3), Some(Ordering::Equal));
        assert_eq!(input3.partial_cmp(&input4), Some(Ordering::Less));
        assert_eq!(input3.partial_cmp(&input5), Some(Ordering::Equal));
        assert_eq!(input3.partial_cmp(&input6), Some(Ordering::Less));

        assert_eq!(input4.partial_cmp(&input1), Some(Ordering::Greater));
        assert_eq!(input4.partial_cmp(&input2), Some(Ordering::Equal));
        assert_eq!(input4.partial_cmp(&input3), Some(Ordering::Greater));
        assert_eq!(input4.partial_cmp(&input4), Some(Ordering::Equal));
        assert_eq!(input4.partial_cmp(&input5), Some(Ordering::Greater));
        assert_eq!(input4.partial_cmp(&input6), Some(Ordering::Equal));

        assert_eq!(input5.partial_cmp(&input1), Some(Ordering::Equal));
        assert_eq!(input5.partial_cmp(&input2), Some(Ordering::Less));
        assert_eq!(input5.partial_cmp(&input3), Some(Ordering::Equal));
        assert_eq!(input5.partial_cmp(&input4), Some(Ordering::Less));
        assert_eq!(input5.partial_cmp(&input5), Some(Ordering::Equal));
        assert_eq!(input5.partial_cmp(&input6), Some(Ordering::Less));

        assert_eq!(input6.partial_cmp(&input1), Some(Ordering::Greater));
        assert_eq!(input6.partial_cmp(&input2), Some(Ordering::Equal));
        assert_eq!(input6.partial_cmp(&input3), Some(Ordering::Greater));
        assert_eq!(input6.partial_cmp(&input4), Some(Ordering::Equal));
        assert_eq!(input6.partial_cmp(&input5), Some(Ordering::Greater));
        assert_eq!(input6.partial_cmp(&input6), Some(Ordering::Equal));
    }
}
