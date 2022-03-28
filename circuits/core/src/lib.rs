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

#![forbid(unsafe_code)]
#![allow(clippy::too_many_arguments)]

#[macro_use]
extern crate enum_index_derive;

pub mod account;
pub mod algorithms;

pub mod helpers;
pub use helpers::*;

use snarkvm_circuits_types::prelude::*;

use core::fmt;
use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{alpha1, alphanumeric1},
    combinator::{map, map_res, recognize},
    multi::{many0, many1},
    sequence::pair,
};
use std::{
    fmt::write,
    io::{Read, Result as IoResult, Write},
};

pub mod identifier;
pub use identifier::*;

pub type Locator = u64;

/// An annotation defines the type parameters for a function or template member.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Annotation<E: Environment> {
    /// A type contains its type name and mode.
    Type(Type<E>),
    /// A composite type contains its identifier.
    Composite(Identifier<E>),
}

impl<E: Environment> Parser for Annotation<E> {
    type Environment = E;

    /// Parses a string into an annotation.
    /// The annotation is of the form `{type_name}.{mode}` or `{identifier}`.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse to determine the annotation (order matters).
        alt((
            map(Type::parse, |type_| Self::Type(type_)),
            map(Identifier::parse, |identifier| Self::Composite(identifier)),
        ))(string)
    }
}

impl<E: Environment> fmt::Display for Annotation<E> {
    /// Prints the annotation as a string.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            // Prints the type, i.e. field.private
            Self::Type(type_) => fmt::Display::fmt(type_, f),
            // Prints the composite type, i.e. record
            Self::Composite(identifier) => fmt::Display::fmt(identifier, f),
        }
    }
}

use indexmap::IndexMap;

/// A value contains the underlying literal(s) in memory.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Value<E: Environment> {
    /// A literal contains its declared literal value.
    Literal(Literal<E>),
    /// A composite literal contains its declared member values.
    Composite(Identifier<E>, Vec<(Identifier<E>, Value<E>)>),
}

impl<E: Environment> Value<E> {
    /// Returns `true` if the value is a constant.
    #[inline]
    pub fn is_constant(&self) -> bool {
        match self {
            Self::Literal(literal) => literal.is_constant(),
            Self::Composite(_, members) => members.iter().all(|(_, value)| value.is_constant()),
        }
    }

    /// Returns the literal corresponding to the given identifier, if `self` is a composite literal.
    /// Returns `None` otherwise.
    #[inline]
    fn get_composite(&self, identifier: &Identifier<E>) -> Option<&Value<E>> {
        match self {
            Self::Composite(_, members) => {
                members.iter().find(|(member, _)| member == identifier).map(|(_, value)| value)
            }
            _ => None,
        }
    }
}

impl<E: Environment> Parser for Value<E> {
    type Environment = E;

    /// Parses a string into a value.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // TODO (howardwu): Sanitize of any whitespaces, or support whitespaces.
        // A composite literal is defined as: `(identifier, [(identifier, value), ...])`,
        // where the left tuple is the name of the composite, and the right tuple is the composite identifiers and value.

        // Parses a tuple of form: (identifier,value).
        let tuple_parse = map(
            pair(pair(tag("("), pair(pair(Identifier::parse, tag(",")), Value::parse)), tag(")")),
            |((_, ((identifier, _), value)), _)| (identifier, value),
        );
        let tuple_parse2 = map(
            pair(pair(tag("("), pair(pair(Identifier::parse, tag(",")), Value::parse)), tag(")")),
            |((_, ((identifier, _), value)), _)| (identifier, value),
        );
        // Parses a sequence of form: (identifier,value),(identifier,value),...,(identifier,value).
        let sequence_parse = map(pair(pair(many0(tuple_parse), tag(",")), tuple_parse2), |((tuples, _), tuple)| {
            let mut tuples = tuples;
            tuples.push(tuple);
            tuples
        });
        // Parses a slice of form: [(identifier,value),(identifier,value),...,(identifier,value)].
        let slice_parse = pair(pair(tag("["), sequence_parse), tag("]"));
        // Parses a composite literal of form: identifier[(identifier, value), ...].
        let composite_literal = map(pair(Identifier::parse, slice_parse), |(identifier, ((_, members), _))| {
            Self::Composite(identifier, members.into_iter().collect())
        });

        // Parse to determine the value (order matters).
        alt((map(Literal::parse, |literal| Self::Literal(literal)), composite_literal))(string)
    }
}

impl<E: Environment> fmt::Display for Value<E> {
    /// Prints the value as a string.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            // Prints the literal, i.e. 10field.private
            Self::Literal(literal) => fmt::Display::fmt(literal, f),
            // Prints the composite literal, i.e. "record"[("owner",aleo1xxx.public),("value",10i64.private)]
            Self::Composite(name, members) => {
                let mut output = format!("{}[", name);
                for (identifier, value) in members.iter() {
                    output += &format!("({identifier},{value}),");
                }
                output.pop(); // trailing comma
                output += &format!("]");

                write!(f, "{output}")
            }
        }
    }
}

use core::cmp::Ordering;

/// A register contains the location data of the underlying value in memory.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Register<E: Environment> {
    /// A register contains its locator in memory.
    /// The register may hold a value or composite value in memory.
    Register(Locator),
    /// A composite register contains its locator and identifier in memory.
    /// The composite register holds a value (that is non-composite) in memory.
    Composite(Locator, Identifier<E>),
}

impl<E: Environment> Register<E> {
    /// Returns the locator of the register.
    #[inline]
    pub fn locator(&self) -> &Locator {
        match self {
            Self::Register(locator) => locator,
            Self::Composite(locator, _) => locator,
        }
    }
}

impl<E: Environment> Parser for Register<E> {
    type Environment = E;

    /// Parses a string into a register.
    /// The register is of the form `r{locator}` or `r{locator}.{identifier}`.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the register character from the string.
        let (string, _) = tag("r")(string)?;
        // Parse the locator from the string.
        let (string, locator) =
            map_res(recognize(many1(one_of("0123456789"))), |locator: &str| locator.parse::<u64>())(string)?;
        // Parse the identifier from the string, if it is a composite register.
        let (string, identifier) = opt(pair(tag("."), Identifier::parse))(string)?;
        // Return the register.
        Ok((string, match identifier {
            Some((_, identifier)) => Self::Composite(locator, identifier),
            None => Self::Register(locator),
        }))
    }
}

impl<E: Environment> fmt::Display for Register<E> {
    /// Prints the register as a string.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            // Prints the register, i.e. r0
            Self::Register(locator) => write!(f, "r{locator}"),
            // Prints the composite register, i.e. r0.owner
            Self::Composite(locator, identifier) => write!(f, "r{locator}.{identifier}"),
        }
    }
}

impl<E: Environment> Ord for Register<E> {
    /// Ordering is determined by the register locator (the identifier is ignored).
    fn cmp(&self, other: &Self) -> Ordering {
        self.locator().cmp(other.locator())
    }
}

impl<E: Environment> PartialOrd for Register<E> {
    /// Ordering is determined by the register locator (the identifier is ignored).
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

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
    /// This function will halt if the given register is of composite format.
    #[inline]
    fn new(register: Register<E>, annotation: Annotation<E>) -> Self {
        // Ensure the register is not a composite register format.
        if let Register::Composite(..) = register {
            E::halt("Input register cannot be of composite format")
        }
        Self { register, annotation }
    }

    /// Returns the input register.
    #[inline]
    fn register(&self) -> &Register<E> {
        &self.register
    }

    /// Returns the input register locator.
    #[inline]
    fn locator(&self) -> &Locator {
        self.register.locator()
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

/// The output statement defines an output of a function.
/// The output may refer to the value in either a register or a composite register.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Output<E: Environment> {
    /// The output register.
    register: Register<E>,
    /// The output annotation.
    annotation: Annotation<E>,
}

impl<E: Environment> Output<E> {
    /// Initializes a new output.
    ///
    /// # Errors
    /// This function will halt if the given register format and annotation format do not match.
    /// If the register is not of composite format, the annotation must also not be of composite format.
    /// If the register is of composite format, the annotation must also be of composite format.
    #[inline]
    fn new(register: Register<E>, annotation: Annotation<E>) -> Self {
        // Ensure the register type and annotation type match.
        match (&register, &annotation) {
            // Case 1: Both are either composite or not composite.
            (Register::Register(..), Annotation::Type(..)) | (Register::Composite(..), Annotation::Composite(..)) => {
                Self { register, annotation }
            }
            // Case 2: Mixed composite and non-composite.
            (Register::Composite(..), Annotation::Type(..)) | (Register::Register(..), Annotation::Composite(..)) => {
                E::halt("Mismatch in output register and annotation declaration")
            }
        }
    }

    /// Returns the output register.
    #[inline]
    fn register(&self) -> &Register<E> {
        &self.register
    }

    /// Returns the input register locator.
    #[inline]
    fn locator(&self) -> &Locator {
        self.register.locator()
    }
}

impl<E: Environment> TypeName for Output<E> {
    /// Returns the type name as a string.
    #[inline]
    fn type_name() -> &'static str {
        "output"
    }
}

impl<E: Environment> Parser for Output<E> {
    type Environment = E;

    /// Parses a string into an output statement.
    /// The output statement is of the form `output {register} {annotation}`.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the output keyword from the string.
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
        // Return the output statement.
        Ok((string, Self { register, annotation }))
    }
}

impl<E: Environment> fmt::Display for Output<E> {
    /// Prints the output statement as a string.
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

/// The operand enum represents the complete set of options for operands in an instruction.
/// This enum is designed to support instructions (such as `add {Register} {Register} {Value}`).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Operand<E: Environment> {
    /// A value contains its declared literal(s).
    Value(Value<E>),
    /// A register contains its locator in memory.
    Register(Register<E>),
}

impl<E: Environment> Operand<E> {
    // /// Returns the value, corresponding to the operand.
    // #[inline]
    // fn load(&self) -> Value<M> {
    //     match self {
    //         Operand::Value(value) => (*value).clone(),
    //         Operand::Register(register) => M::load(register),
    //     }
    // }

    /// Returns the value, if the operand is a value.
    /// Returns `None` otherwise.
    ///
    /// # Examples
    /// ```
    /// use snarkvm_circuits_core::{Register, Operand, Value, Literal};
    /// use snarkvm_circuits_types::environment::{Parser, Circuit};
    /// let operand = Operand::<Circuit>::Value(Value::Literal(Literal::from_str("1field.private")));
    /// assert_eq!(operand.value(), Some(&Value::Literal(Literal::from_str("1field.private"))));
    /// ```
    /// ```
    /// use snarkvm_circuits_core::{Register, Operand};
    /// use snarkvm_circuits_types::environment::{Parser, Circuit};
    /// let operand = Operand::<Circuit>::Register(Register::from_str("r0"));
    /// assert_eq!(operand.value(), None);
    /// ```
    #[inline]
    pub fn value(&self) -> Option<&Value<E>> {
        match self {
            Operand::Value(value) => Some(value),
            _ => None,
        }
    }

    /// Returns the register, if the operand is a register.
    /// Returns `None` otherwise.
    ///
    /// # Examples
    /// ```
    /// use snarkvm_circuits_core::{Register, Operand};
    /// use snarkvm_circuits_types::environment::{Parser, Circuit};
    /// let operand = Operand::<Circuit>::Register(Register::from_str("r0"));
    /// assert_eq!(operand.register(), Some(&Register::from_str("r0")));
    /// ```
    /// ```
    /// use snarkvm_circuits_core::{Register, Operand, Value, Literal};
    /// use snarkvm_circuits_types::environment::{Parser, Circuit};
    /// let operand = Operand::<Circuit>::Value(Value::Literal(Literal::from_str("1field.private")));
    /// assert_eq!(operand.register(), None);
    /// ```
    #[inline]
    pub fn register(&self) -> Option<&Register<E>> {
        match self {
            Operand::Register(register) => Some(register),
            _ => None,
        }
    }

    /// Returns `true` if the operand is a value.
    /// Returns `false` if the operand is a register.
    #[inline]
    pub fn is_value(&self) -> bool {
        matches!(self, Operand::Value(_))
    }

    /// Returns `true` if the operand is a register.
    /// Returns `false` if the operand is a value.
    #[inline]
    pub fn is_register(&self) -> bool {
        matches!(self, Operand::Register(_))
    }
}

impl<E: Environment> Parser for Operand<E> {
    type Environment = E;

    /// Parses a string into a operand.
    ///
    /// # Examples
    /// ```
    /// use snarkvm_circuits_core::{Register, Operand, Value, Literal};
    /// use snarkvm_circuits_types::environment::{Parser, Circuit};
    /// let operand = Operand::<Circuit>::Value(Value::Literal(Literal::from_str("1field.private")));
    /// assert_eq!(Operand::<Circuit>::parse("1field.private"), Ok(("", Operand::Value(Value::Literal(Literal::from_str("1field.private"))))));
    /// ```
    /// ```
    /// use snarkvm_circuits_core::{Operand, Register};
    /// use snarkvm_circuits_types::environment::{Parser, Circuit};
    /// let operand = Operand::<Circuit>::Register(Register::from_str("r0"));
    /// assert_eq!(Operand::<Circuit>::parse("r0"), Ok(("", Operand::Register(Register::from_str("r0")))));
    /// ```
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse to determine the operand (order matters).
        alt((map(Value::parse, |value| Self::Value(value)), map(Register::parse, |register| Self::Register(register))))(
            string,
        )
    }
}

impl<E: Environment> fmt::Display for Operand<E> {
    /// Prints the operand as a string.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            // Prints the value, i.e. 10field.private
            Self::Value(literal) => literal.fmt(f),
            // Prints the register, i.e. r0 or r0.owner
            Self::Register(register) => register.fmt(f),
        }
    }
}

/// The instruction represents a single instruction in the program.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Instruction<E: Environment> {
    /// The instruction name.
    name: &'static str,
    /// The destination register.
    destination: Register<E>,
    /// The operands of the instruction.
    operands: Vec<Operand<E>>,
}

impl<E: Environment> Instruction<E> {
    /// Initializes a new instruction.
    ///
    /// # Errors
    /// This function will halt if the given destination register is of composite format.
    #[inline]
    pub fn new(name: &'static str, destination: Register<E>, operands: Vec<Operand<E>>) -> Self {
        // Ensure the destination register is not a composite register format.
        if let Register::Composite(..) = destination {
            E::halt("Destination register cannot be of composite format")
        }
        Self { name, destination, operands }
    }

    /// Returns the instruction name.
    /// This is the name of the instruction, such as `add`.
    #[inline]
    pub fn name(&self) -> &'static str {
        self.name
    }

    /// Returns the destination register.
    /// This is the register that the instruction will write its result into.
    #[inline]
    pub fn destination(&self) -> &Register<E> {
        &self.destination
    }

    /// Returns the operands of the instruction.
    /// These are the registers and values that the instruction will read from.
    #[inline]
    pub fn operands(&self) -> &[Operand<E>] {
        &self.operands
    }
}

impl<E: Environment> fmt::Display for Instruction<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{} {} {}",
            self.name,
            self.destination,
            self.operands.iter().map(|operand| operand.to_string()).collect::<Vec<_>>().join(" ")
        )
    }
}

pub trait Memory: Environment {
    /// Loads the value of a given register from memory.
    ///
    /// # Errors
    /// This function will halt if the register locator is not found.
    /// In the case of composite registers, this function will halt if the identifier is not found.
    fn load(register: &Register<Self>) -> Value<Self>;

    /// Stores the given register and value in memory, assuming the register has not been previously stored.
    ///
    /// # Errors
    /// This function will halt if the register was previously stored.
    fn store(register: &Register<Self>, value: Value<Self>);

    /// Adds the input statement into memory.
    /// This method is called before a function is run.
    /// This method is only called before `new_instruction` is ever called.
    ///
    /// # Errors
    /// This method will halt if the given input register is not new.
    /// This method will halt if the given inputs are not incrementing monotonically.
    fn new_input_statement(input: Input<Self>);

    /// Assigns the given input value to the corresponding register in memory.
    /// This method is called before a function is run.
    ///
    /// # Errors
    /// This function will halt if the input registers are not assigned monotonically.
    /// This function will halt if the input register was previously stored.
    /// This function will also halt if the register is not an input register.
    fn assign_input(input: Input<Self>, value: Value<Self>);

    /// Adds the output statement into memory.
    /// This method is called before a function is run.
    ///
    /// # Errors
    /// This method will halt if the given output register is new.
    /// This method will halt if the given output register is already set.
    fn new_output_statement(output: Output<Self>);
}

use indexmap::IndexSet;

pub struct Stack<E: Environment> {
    /// The map of register locators to their values.
    /// When input statements are added, a new entry of `(locator, None)` is added to this map.
    /// When input assignments are added, the entry is updated to `(locator, Some(value))`.
    /// No changes occur to `registers` when output statements are added.
    registers: IndexMap<Locator, Option<Value<E>>>,
    /// The input statements, added in order of the input registers.
    /// Input assignments are ensured to match the ordering of the input statements.
    input_statements: IndexSet<Input<E>>,
    /// The instructions, in order of execution.
    instructions: IndexSet<Instruction<E>>,
    /// The output statements, in order of the desired output.
    /// There is no expectation that the output registers are in any ordering.
    output_statements: IndexSet<Output<E>>,
}

impl<E: Environment> Stack<E> {
    /// Loads the value of a given register from memory.
    ///
    /// # Errors
    /// This function will halt if the register locator is not found.
    /// In the case of composite registers, this function will halt if the identifier is not found.
    #[inline]
    fn load(&self, register: &Register<E>) -> Value<E> {
        // Attempt to load the value from the register.
        let candidate = match register {
            // Load the value for a register.
            Register::Register(locator) => self.registers.get(locator),
            // Load the value for a composite.
            Register::Composite(locator, _) => self.registers.get(locator),
        };

        // Retrieve the value from the option.
        let value = match candidate {
            // Return the value if it exists.
            Some(Some(value)) => value,
            // Halts if the value does not exist.
            Some(None) | None => E::halt(format!("Failed to locate register {register}")),
        };

        // If the register is a composite register, then load the specific value from the composite literal.
        match register {
            // Load the value for a register.
            Register::Register(_) => (*value).clone(),
            // Load the value for a composite.
            Register::Composite(locator, identifier) => match value.get_composite(identifier) {
                // Return the value if it exists.
                Some(value) => (*value).clone(),
                // Halts if the value in the composite literal does not exist.
                None => E::halt(format!("Failed to locate composite {identifier} in register {locator}")),
            },
        }
    }

    /// Stores the given register and value in memory, assuming the register has not been previously stored.
    ///
    /// # Errors
    /// This function will halt if the register was previously stored.
    #[inline]
    fn store(&mut self, register: &Register<E>, value: Value<E>) {
        // Store the value in the register.
        let previous = match register {
            // Store the value for a register.
            Register::Register(locator) => self.registers.insert(locator.clone(), Some(value)),
            // Store the value for a composite.
            Register::Composite(locator, _) => self.registers.insert(locator.clone(), Some(value)),
        };

        // Ensure the register has not been previously stored.
        if let Some(Some(..)) = previous {
            E::halt(format!("Register {} was previously stored", register.locator()))
        }
    }

    /// Adds the input statement into memory.
    /// This method is called before a function is run.
    /// This method is only called before `new_instruction` is ever called.
    ///
    /// # Errors
    /// This method will halt if the given input register is not new.
    /// This method will halt if the given inputs are not incrementing monotonically.
    #[inline]
    fn new_input_statement(&mut self, input: Input<E>) {
        // Ensure the input does not exist in the registers.
        if self.registers.contains_key(input.locator()) {
            E::halt(format!("Input register {} was previously stored", input.locator()))
        }

        // Ensure the input register is new, and incrementing monotonically.
        // This operation is only performed before the new variables are created,
        // so the performance of this operation should be reasonable.
        let mut index = 0;
        while self.registers.contains_key(&index) {
            index += 1;
        }
        if index != *input.locator() {
            E::halt(format!("Invalid input ordering detected in memory at register {index}"))
        }

        // Insert the input statement to memory.
        self.input_statements.insert(input);
    }

    /// Assigns the given input value to the corresponding register in memory.
    /// This method is called before a function is run.
    ///
    /// # Errors
    /// This function will halt if the input registers are not assigned monotonically.
    /// This function will halt if the input register was previously stored.
    /// This function will halt if the register is not an input register.
    #[inline]
    fn assign_input(&mut self, input: Input<E>, value: Value<E>) {
        // Ensure the input exists in the registers.
        if !self.registers.contains_key(input.locator()) {
            E::halt(format!("Register {} does not exist", input.locator()))
        }

        // Ensure the input exists in the inputs.
        if !self.input_statements.contains(&input) {
            E::halt(format!("Input register {} does not exist", input.locator()))
        }

        // Ensure the previous input is assigned before the current input.
        match self.registers.get(&input.locator().saturating_sub(1)) {
            Some(None) | None => E::halt(format!(
                "Cannot assign input register {} as the previous register is not assigned yet",
                input.locator()
            )),
            _ => (),
        }

        // Assign the input value to the register.
        if let Some(Some(..)) = self.registers.insert(*input.locator(), Some(value)) {
            E::halt(format!("Input register {} was already assigned", input.locator()))
        }
    }

    /// Adds the given instruction into memory.
    /// This method is called before a function is run.
    ///
    /// # Errors
    /// This method will halt if the given instruction already exists in memory.
    /// This method will halt if the destination register already exists in memory.
    /// This method will halt if the destination register locator does not monotonically increase.
    /// This method will halt if any operand register does not already exist in memory.
    /// This method will halt if any operand registers are greater than *or equal to* the destination register.
    /// This method will halt if any registers are already set.
    /// This method will halt if any operand values are not constant.
    #[inline]
    fn new_instruction(&mut self, instruction: Instruction<E>) {
        // Ensure the instruction does not already exist in memory.
        if self.instructions.contains(&instruction) {
            E::halt(format!("Instruction {} was previously stored", instruction))
        }

        // Ensure the destination register does not exist.
        if self.registers.contains_key(instruction.destination.locator()) {
            E::halt(format!("Destination {} already exists", instruction.destination))
        }

        // Ensure the destination register locator is monotonically increasing.
        if !self.registers.contains_key(&instruction.destination.locator().saturating_sub(1)) {
            E::halt(format!("Destination {} is not monotonically increasing", instruction.destination))
        }

        // Ensure the operand registers exist.
        for register in instruction.operands().iter().filter_map(|operand| operand.register()) {
            if !self.registers.contains_key(register.locator()) {
                E::halt(format!("Operand register {} does not exist", register))
            }
        }

        // Ensure the operands do not contain registers greater than or equal to the destination register.
        for register in instruction.operands().iter().filter_map(|operand| operand.register()) {
            if *register.locator() >= *instruction.destination.locator() {
                E::halt(format!(
                    "Operand register {} is greater than the destination {}",
                    register, instruction.destination
                ))
            }
        }

        // Ensure the destination register and operand registers are not already set.
        for register in [instruction.destination.clone()]
            .iter()
            .chain(instruction.operands().iter().filter_map(|operand| operand.register()))
        {
            if let Some(Some(..)) = self.registers.get(register.locator()) {
                E::halt(format!("Register {} is already set", register))
            }
        }

        // Ensure the operand values are constant.
        for value in instruction.operands().iter().filter_map(|operand| operand.value()) {
            if !value.is_constant() {
                E::halt(format!("Operand {} is not constant", value))
            }
        }

        // Add the instruction to the memory.
        self.instructions.insert(instruction);
    }

    /// Adds the output statement into memory.
    /// This method is called before a function is run.
    ///
    /// # Errors
    /// This method will halt if the given output register is new.
    /// This method will halt if the given output register is already set.
    #[inline]
    fn new_output_statement(&mut self, output: Output<E>) {
        // Ensure the output exists in the registers.
        if !self.registers.contains_key(output.locator()) {
            E::halt(format!("Output register {} is missing", output.locator()))
        }

        // Ensure the output register is not already set.
        if let Some(Some(..)) = self.registers.get(output.locator()) {
            E::halt(format!("Output register {} was already set", output.locator()))
        }

        // Insert the output statement to memory.
        self.output_statements.insert(output);
    }
}

// enum Declaration<E> {
//     /// A template declaration.
//     Template(Identifier<E>),
//     /// A function declaration.
//     Function(Identifier<E>),
// }

// pub struct Template<E: Environment>(Identifier<E>);
//
// impl<E: Environment> Parser for Template<E> {
//     type Environment = E;
//
//     /// Parses a string into a template.
//     #[inline]
//     fn parse(string: &str) -> ParserResult<Self> {
//         let (string, template_name) = Identifier::parse(string)?;
//         Ok((string, Self(template_name)))
//     }
// }
