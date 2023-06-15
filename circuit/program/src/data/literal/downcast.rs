// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use super::*;

impl<A: Aleo> Literal<A> {
    /// Downcasts the literal to the given literal type.
    ///
    /// This method checks that the downcast does not lose any bits of information,
    /// and returns an error if it does.
    ///
    /// The hierarchy of downcasting is as follows:
    ///  - (`Address`, `Group`) -> `Field` -> `Scalar` -> `Integer` -> `Boolean`
    ///  - `String` (not supported)
    pub fn downcast(&self, to_type: LiteralType) -> Result<Self> {
        match self {
            Self::Address(address) => downcast_group_to_type(address.to_group(), to_type),
            Self::Boolean(..) => bail!("Cannot downcast a boolean literal to another type."),
            Self::Field(field) => downcast_field_to_type(field.clone(), to_type),
            Self::Group(group) => downcast_group_to_type(group.clone(), to_type),
            Self::I8(..) => bail!("Cannot downcast an i8 literal to another type (yet)."),
            Self::I16(..) => bail!("Cannot downcast an i16 literal to another type (yet)."),
            Self::I32(..) => bail!("Cannot downcast an i32 literal to another type (yet)."),
            Self::I64(..) => bail!("Cannot downcast an i64 literal to another type (yet)."),
            Self::I128(..) => bail!("Cannot downcast an i128 literal to another type (yet)."),
            Self::U8(..) => bail!("Cannot downcast a u8 literal to another type (yet)."),
            Self::U16(..) => bail!("Cannot downcast a u16 literal to another type (yet)."),
            Self::U32(..) => bail!("Cannot downcast a u32 literal to another type (yet)."),
            Self::U64(..) => bail!("Cannot downcast a u64 literal to another type (yet)."),
            Self::U128(..) => bail!("Cannot downcast a u128 literal to another type (yet)."),
            Self::Scalar(..) => bail!("Cannot downcast a scalar literal to another type (yet)."),
            Self::Signature(..) => bail!("Cannot downcast a signature literal to another type."),
            Self::String(..) => bail!("Cannot downcast a string literal to another type."),
        }
    }

    /// Downcasts the literal to the given literal type, with lossy truncation.
    ///
    /// This method makes a *best-effort* attempt to preserve upcasting back
    /// to the original literal type, but it is not guaranteed to do so.
    ///
    /// The hierarchy of downcasting is as follows:
    ///  - (`Address`, `Group`) -> `Field` -> `Scalar` -> `Integer` -> `Boolean`
    ///  - `String` (not supported)
    pub fn downcast_lossy(&self, to_type: LiteralType) -> Result<Self> {
        match self {
            Self::Address(address) => downcast_lossy_group_to_type(address.to_group(), to_type),
            Self::Boolean(..) => bail!("Cannot downcast a boolean literal to another type."),
            Self::Field(field) => downcast_lossy_field_to_type(field.clone(), to_type),
            Self::Group(group) => downcast_lossy_group_to_type(group.clone(), to_type),
            Self::I8(..) => bail!("Cannot downcast an i8 literal to another type (yet)."),
            Self::I16(..) => bail!("Cannot downcast an i16 literal to another type (yet)."),
            Self::I32(..) => bail!("Cannot downcast an i32 literal to another type (yet)."),
            Self::I64(..) => bail!("Cannot downcast an i64 literal to another type (yet)."),
            Self::I128(..) => bail!("Cannot downcast an i128 literal to another type (yet)."),
            Self::U8(..) => bail!("Cannot downcast a u8 literal to another type (yet)."),
            Self::U16(..) => bail!("Cannot downcast a u16 literal to another type (yet)."),
            Self::U32(..) => bail!("Cannot downcast a u32 literal to another type (yet)."),
            Self::U64(..) => bail!("Cannot downcast a u64 literal to another type (yet)."),
            Self::U128(..) => bail!("Cannot downcast a u128 literal to another type (yet)."),
            Self::Scalar(..) => bail!("Cannot downcast a scalar literal to another type (yet)."),
            Self::Signature(..) => bail!("Cannot downcast a signature literal to another type."),
            Self::String(..) => bail!("Cannot downcast a string literal to another type."),
        }
    }
}

/// Downcasts a field literal to the given literal type.
fn downcast_field_to_type<A: Aleo>(field: Field<A>, to_type: LiteralType) -> Result<Literal<A>> {
    match to_type {
        LiteralType::Address => bail!("Cannot downcast a field literal to an address type."),
        LiteralType::Boolean => bail!("Cannot downcast a field literal to a boolean type (yet)."),
        LiteralType::Field => Ok(Literal::Field(field)),
        LiteralType::Group => bail!("Cannot downcast a field literal to a group type."),
        LiteralType::I8 => Ok(Literal::I8(I8::from_field(field))),
        LiteralType::I16 => Ok(Literal::I16(I16::from_field(field))),
        LiteralType::I32 => Ok(Literal::I32(I32::from_field(field))),
        LiteralType::I64 => Ok(Literal::I64(I64::from_field(field))),
        LiteralType::I128 => Ok(Literal::I128(I128::from_field(field))),
        LiteralType::U8 => Ok(Literal::U8(U8::from_field(field))),
        LiteralType::U16 => Ok(Literal::U16(U16::from_field(field))),
        LiteralType::U32 => Ok(Literal::U32(U32::from_field(field))),
        LiteralType::U64 => Ok(Literal::U64(U64::from_field(field))),
        LiteralType::U128 => Ok(Literal::U128(U128::from_field(field))),
        LiteralType::Scalar => Ok(Literal::Scalar(Scalar::from_field(field))),
        LiteralType::Signature => bail!("Cannot downcast a field literal to a signature type."),
        LiteralType::String => bail!("Cannot downcast a field literal to a string type."),
    }
}

/// Downcasts a field literal to the given literal type, with lossy truncation.
fn downcast_lossy_field_to_type<A: Aleo>(field: Field<A>, to_type: LiteralType) -> Result<Literal<A>> {
    match to_type {
        LiteralType::Address => bail!("Cannot downcast a field literal to an address type."),
        LiteralType::Boolean => bail!("Cannot downcast a field literal to a boolean type (yet)."),
        LiteralType::Field => Ok(Literal::Field(field)),
        LiteralType::Group => bail!("Cannot downcast a field literal to a group type."),
        LiteralType::I8 => Ok(Literal::I8(I8::from_field_lossy(field))),
        LiteralType::I16 => Ok(Literal::I16(I16::from_field_lossy(field))),
        LiteralType::I32 => Ok(Literal::I32(I32::from_field_lossy(field))),
        LiteralType::I64 => Ok(Literal::I64(I64::from_field_lossy(field))),
        LiteralType::I128 => Ok(Literal::I128(I128::from_field_lossy(field))),
        LiteralType::U8 => Ok(Literal::U8(U8::from_field_lossy(field))),
        LiteralType::U16 => Ok(Literal::U16(U16::from_field_lossy(field))),
        LiteralType::U32 => Ok(Literal::U32(U32::from_field_lossy(field))),
        LiteralType::U64 => Ok(Literal::U64(U64::from_field_lossy(field))),
        LiteralType::U128 => Ok(Literal::U128(U128::from_field_lossy(field))),
        LiteralType::Scalar => Ok(Literal::Scalar(Scalar::from_field_lossy(field))),
        LiteralType::Signature => bail!("Cannot downcast a field literal to a signature type."),
        LiteralType::String => bail!("Cannot downcast a field literal to a string type."),
    }
}

/// Downcasts a group literal to the given literal type.
fn downcast_group_to_type<A: Aleo>(group: Group<A>, to_type: LiteralType) -> Result<Literal<A>> {
    match to_type {
        LiteralType::Address => Ok(Literal::Address(Address::from_group(group))),
        LiteralType::Group => Ok(Literal::Group(group)),
        _ => downcast_field_to_type(group.to_x_coordinate(), to_type),
    }
}

/// Downcasts a group literal to the given literal type, with lossy truncation.
fn downcast_lossy_group_to_type<A: Aleo>(group: Group<A>, to_type: LiteralType) -> Result<Literal<A>> {
    match to_type {
        LiteralType::Address => Ok(Literal::Address(Address::from_group(group))),
        LiteralType::Group => Ok(Literal::Group(group)),
        _ => downcast_lossy_field_to_type(group.to_x_coordinate(), to_type),
    }
}

#[cfg(test)]
mod test {
    use crate::{count_is, Literal};

    use console::{LiteralType, TestRng, Uniform};
    use snarkvm_circuit_network::AleoV0;
    use snarkvm_circuit_types::{
        environment::{Circuit, UpdatableCount},
        Eject,
        Environment,
        Inject,
        Mode,
    };

    type CurrentAleo = AleoV0;

    const ITERATIONS: usize = 100;

    fn test_downcast(
        mut sample_literal: impl FnMut() -> console::Literal<<CurrentAleo as Environment>::Network>,
        mode: Mode,
        to_type: LiteralType,
        count: UpdatableCount,
    ) {
        for i in 0..ITERATIONS {
            let console_literal = sample_literal();
            let circuit_literal = Literal::<CurrentAleo>::new(mode, console_literal.clone());
            let expected = std::panic::catch_unwind(|| console_literal.downcast(to_type).unwrap());
            match mode {
                Mode::Constant if expected.is_err() => {
                    assert!(std::panic::catch_unwind(|| circuit_literal.downcast(to_type).unwrap()).is_err())
                }
                _ => Circuit::scope(&format!("downcast_{:?}_to_{to_type}_{i}", console_literal.to_type()), || {
                    let downcasted = circuit_literal.downcast(to_type).unwrap();
                    match expected {
                        Err(_) => assert!(!Circuit::is_satisfied()),
                        Ok(expected) => {
                            assert!(Circuit::is_satisfied());
                            assert_eq!(downcasted.eject_value(), expected);
                        }
                    }
                    count.assert_matches(
                        Circuit::num_constants_in_scope(),
                        Circuit::num_public_in_scope(),
                        Circuit::num_private_in_scope(),
                        Circuit::num_constraints_in_scope(),
                    );
                }),
            };
            Circuit::reset();
        }
    }

    fn test_downcast_lossy(
        mut sample_literal: impl FnMut() -> console::Literal<<CurrentAleo as Environment>::Network>,
        mode: Mode,
        to_type: LiteralType,
        count: UpdatableCount,
    ) {
        for i in 0..ITERATIONS {
            let console_literal = sample_literal();
            let circuit_literal = Literal::<CurrentAleo>::new(mode, console_literal.clone());
            let expected = std::panic::catch_unwind(|| console_literal.downcast_lossy(to_type).unwrap());
            match mode {
                Mode::Constant if expected.is_err() => {
                    assert!(std::panic::catch_unwind(|| circuit_literal.downcast_lossy(to_type).unwrap()).is_err())
                }
                _ => {
                    Circuit::scope(&format!("downcast_lossy_{:?}_to_{to_type}_{i}", console_literal.to_type()), || {
                        let downcasted = circuit_literal.downcast_lossy(to_type).unwrap();
                        match expected {
                            Err(_) => assert!(!Circuit::is_satisfied()),
                            Ok(expected) => {
                                assert!(Circuit::is_satisfied());
                                assert_eq!(downcasted.eject_value(), expected);
                            }
                        }
                        count.assert_matches(
                            Circuit::num_constants_in_scope(),
                            Circuit::num_public_in_scope(),
                            Circuit::num_private_in_scope(),
                            Circuit::num_constraints_in_scope(),
                        );
                    })
                }
            };
            Circuit::reset();
        }
    }

    macro_rules! test {
        ($cast:ident, Address, $output:ident, $mode:ident, $count:expr) => {
            paste::paste! {
                #[test]
                fn [<test_ $cast _ $mode:lower _address_to_ $output:lower>]() {
                    let rng = &mut TestRng::default();
                    [<test_ $cast>](|| console::Literal::Address(console::Address::new(Uniform::rand(rng))), Mode::$mode, LiteralType::$output, $count)
                }
            }
        };
        ($cast:ident, $input:ident, $output:ident, $mode:ident, $count:expr) => {
            paste::paste! {
                #[test]
                fn [<test_ $cast _ $mode:lower _ $input:lower _to_ $output:lower>]() {
                    let rng = &mut TestRng::default();
                    [<test_ $cast>](|| console::Literal::$input(Uniform::rand(rng)), Mode::$mode, LiteralType::$output, $count)
                }
            }
        }
    }

    // Downcast from Address to Address.
    test!(downcast, Address, Address, Constant, count_is!(0, 0, 0, 0));
    test!(downcast, Address, Address, Public, count_is!(0, 0, 0, 0));
    test!(downcast, Address, Address, Private, count_is!(0, 0, 0, 0));
    test!(downcast_lossy, Address, Address, Constant, count_is!(0, 0, 0, 0));
    test!(downcast_lossy, Address, Address, Public, count_is!(0, 0, 0, 0));
    test!(downcast_lossy, Address, Address, Private, count_is!(0, 0, 0, 0));

    // TODO: Downcast from Address to Boolean.

    // Downcast from Address to Field.
    test!(downcast, Address, Field, Constant, count_is!(0, 0, 0, 0));
    test!(downcast, Address, Field, Public, count_is!(0, 0, 0, 0));
    test!(downcast, Address, Field, Private, count_is!(0, 0, 0, 0));
    test!(downcast_lossy, Address, Field, Constant, count_is!(0, 0, 0, 0));
    test!(downcast_lossy, Address, Field, Public, count_is!(0, 0, 0, 0));
    test!(downcast_lossy, Address, Field, Private, count_is!(0, 0, 0, 0));

    // Downcast from Address to Group.
    test!(downcast, Address, Group, Constant, count_is!(0, 0, 0, 0));
    test!(downcast, Address, Group, Public, count_is!(0, 0, 0, 0));
    test!(downcast, Address, Group, Private, count_is!(0, 0, 0, 0));
    test!(downcast_lossy, Address, Group, Constant, count_is!(0, 0, 0, 0));
    test!(downcast_lossy, Address, Group, Public, count_is!(0, 0, 0, 0));
    test!(downcast_lossy, Address, Group, Private, count_is!(0, 0, 0, 0));

    // Downcast from Address to I8
    test!(downcast, Address, I8, Constant, count_is!(0, 0, 0, 0));
    test!(downcast, Address, I8, Public, count_is!(0, 0, 8, 9));
    test!(downcast, Address, I8, Private, count_is!(0, 0, 8, 9));
    test!(downcast_lossy, Address, I8, Constant, count_is!(253, 0, 0, 0));
    test!(downcast_lossy, Address, I8, Public, count_is!(0, 0, 505, 507));
    test!(downcast_lossy, Address, I8, Private, count_is!(0, 0, 505, 507));

    // Downcast from Address to I16
    test!(downcast, Address, I16, Constant, count_is!(0, 0, 0, 0));
    test!(downcast, Address, I16, Public, count_is!(0, 0, 16, 17));
    test!(downcast, Address, I16, Private, count_is!(0, 0, 16, 17));
    test!(downcast_lossy, Address, I16, Constant, count_is!(253, 0, 0, 0));
    test!(downcast_lossy, Address, I16, Public, count_is!(0, 0, 505, 507));
    test!(downcast_lossy, Address, I16, Private, count_is!(0, 0, 505, 507));

    // Downcast from Address to I32
    test!(downcast, Address, I32, Constant, count_is!(0, 0, 0, 0));
    test!(downcast, Address, I32, Public, count_is!(0, 0, 32, 33));
    test!(downcast, Address, I32, Private, count_is!(0, 0, 32, 33));
    test!(downcast_lossy, Address, I32, Constant, count_is!(253, 0, 0, 0));
    test!(downcast_lossy, Address, I32, Public, count_is!(0, 0, 505, 507));

    // Downcast from Address to I64
    test!(downcast, Address, I64, Constant, count_is!(0, 0, 0, 0));
    test!(downcast, Address, I64, Public, count_is!(0, 0, 64, 65));
    test!(downcast, Address, I64, Private, count_is!(0, 0, 64, 65));
    test!(downcast_lossy, Address, I64, Constant, count_is!(253, 0, 0, 0));
    test!(downcast_lossy, Address, I64, Public, count_is!(0, 0, 505, 507));
    test!(downcast_lossy, Address, I64, Private, count_is!(0, 0, 505, 507));

    // Downcast from Address to I128
    test!(downcast, Address, I128, Constant, count_is!(0, 0, 0, 0));
    test!(downcast, Address, I128, Public, count_is!(0, 0, 128, 129));
    test!(downcast, Address, I128, Private, count_is!(0, 0, 128, 129));
    test!(downcast_lossy, Address, I128, Constant, count_is!(253, 0, 0, 0));
    test!(downcast_lossy, Address, I128, Public, count_is!(0, 0, 505, 507));
    test!(downcast_lossy, Address, I128, Private, count_is!(0, 0, 505, 507));

    // Downcast from Address to U8
    test!(downcast, Address, U8, Constant, count_is!(0, 0, 0, 0));
    test!(downcast, Address, U8, Public, count_is!(0, 0, 8, 9));
    test!(downcast, Address, U8, Private, count_is!(0, 0, 8, 9));
    test!(downcast_lossy, Address, U8, Constant, count_is!(253, 0, 0, 0));
    test!(downcast_lossy, Address, U8, Public, count_is!(0, 0, 505, 507));
    test!(downcast_lossy, Address, U8, Private, count_is!(0, 0, 505, 507));

    // Downcast from Address to U16
    test!(downcast, Address, U16, Constant, count_is!(0, 0, 0, 0));
    test!(downcast, Address, U16, Public, count_is!(0, 0, 16, 17));
    test!(downcast, Address, U16, Private, count_is!(0, 0, 16, 17));
    test!(downcast_lossy, Address, U16, Constant, count_is!(253, 0, 0, 0));
    test!(downcast_lossy, Address, U16, Public, count_is!(0, 0, 505, 507));
    test!(downcast_lossy, Address, U16, Private, count_is!(0, 0, 505, 507));

    // Downcast from Address to U32
    test!(downcast, Address, U32, Constant, count_is!(0, 0, 0, 0));
    test!(downcast, Address, U32, Public, count_is!(0, 0, 32, 33));
    test!(downcast, Address, U32, Private, count_is!(0, 0, 32, 33));
    test!(downcast_lossy, Address, U32, Constant, count_is!(253, 0, 0, 0));
    test!(downcast_lossy, Address, U32, Public, count_is!(0, 0, 505, 507));

    // Downcast from Address to U64
    test!(downcast, Address, U64, Constant, count_is!(0, 0, 0, 0));
    test!(downcast, Address, U64, Public, count_is!(0, 0, 64, 65));
    test!(downcast, Address, U64, Private, count_is!(0, 0, 64, 65));
    test!(downcast_lossy, Address, U64, Constant, count_is!(253, 0, 0, 0));
    test!(downcast_lossy, Address, U64, Public, count_is!(0, 0, 505, 507));
    test!(downcast_lossy, Address, U64, Private, count_is!(0, 0, 505, 507));

    // Downcast from Address to U128
    test!(downcast, Address, U128, Constant, count_is!(0, 0, 0, 0));
    test!(downcast, Address, U128, Public, count_is!(0, 0, 128, 129));
    test!(downcast, Address, U128, Private, count_is!(0, 0, 128, 129));
    test!(downcast_lossy, Address, U128, Constant, count_is!(253, 0, 0, 0));
    test!(downcast_lossy, Address, U128, Public, count_is!(0, 0, 505, 507));
    test!(downcast_lossy, Address, U128, Private, count_is!(0, 0, 505, 507));

    // Downcast from Address to Scalar.
    test!(downcast, Address, Scalar, Constant, count_is!(253, 0, 0, 0));
    test!(downcast, Address, Scalar, Public, count_is!(0, 0, 755, 760));
    test!(downcast, Address, Scalar, Private, count_is!(0, 0, 755, 760));
    test!(downcast_lossy, Address, Scalar, Constant, count_is!(253, 0, 0, 0));
    test!(downcast_lossy, Address, Scalar, Public, count_is!(0, 0, 505, 507));
    test!(downcast_lossy, Address, Scalar, Private, count_is!(0, 0, 505, 507));

    // Downcast from Group to Address.
    test!(downcast, Group, Address, Constant, count_is!(0, 0, 0, 0));
    test!(downcast, Group, Address, Public, count_is!(0, 0, 0, 0));
    test!(downcast, Group, Address, Private, count_is!(0, 0, 0, 0));
    test!(downcast_lossy, Group, Address, Constant, count_is!(0, 0, 0, 0));
    test!(downcast_lossy, Group, Address, Public, count_is!(0, 0, 0, 0));
    test!(downcast_lossy, Group, Address, Private, count_is!(0, 0, 0, 0));

    // TODO: Downcast from Group to Boolean.

    // Downcast from Group to Field.
    test!(downcast, Group, Field, Constant, count_is!(0, 0, 0, 0));
    test!(downcast, Group, Field, Public, count_is!(0, 0, 0, 0));
    test!(downcast, Group, Field, Private, count_is!(0, 0, 0, 0));
    test!(downcast_lossy, Group, Field, Constant, count_is!(0, 0, 0, 0));
    test!(downcast_lossy, Group, Field, Public, count_is!(0, 0, 0, 0));
    test!(downcast_lossy, Group, Field, Private, count_is!(0, 0, 0, 0));

    // Downcast from Group to Group.
    test!(downcast, Group, Group, Constant, count_is!(0, 0, 0, 0));
    test!(downcast, Group, Group, Public, count_is!(0, 0, 0, 0));
    test!(downcast, Group, Group, Private, count_is!(0, 0, 0, 0));
    test!(downcast_lossy, Group, Group, Constant, count_is!(0, 0, 0, 0));
    test!(downcast_lossy, Group, Group, Public, count_is!(0, 0, 0, 0));
    test!(downcast_lossy, Group, Group, Private, count_is!(0, 0, 0, 0));

    // Downcast from Group to I8
    test!(downcast, Group, I8, Constant, count_is!(0, 0, 0, 0));
    test!(downcast, Group, I8, Public, count_is!(0, 0, 8, 9));
    test!(downcast, Group, I8, Private, count_is!(0, 0, 8, 9));
    test!(downcast_lossy, Group, I8, Constant, count_is!(253, 0, 0, 0));
    test!(downcast_lossy, Group, I8, Public, count_is!(0, 0, 505, 507));
    test!(downcast_lossy, Group, I8, Private, count_is!(0, 0, 505, 507));

    // Downcast from Group to I16
    test!(downcast, Group, I16, Constant, count_is!(0, 0, 0, 0));
    test!(downcast, Group, I16, Public, count_is!(0, 0, 16, 17));
    test!(downcast, Group, I16, Private, count_is!(0, 0, 16, 17));
    test!(downcast_lossy, Group, I16, Constant, count_is!(253, 0, 0, 0));
    test!(downcast_lossy, Group, I16, Public, count_is!(0, 0, 505, 507));
    test!(downcast_lossy, Group, I16, Private, count_is!(0, 0, 505, 507));

    // Downcast from Group to I32
    test!(downcast, Group, I32, Constant, count_is!(0, 0, 0, 0));
    test!(downcast, Group, I32, Public, count_is!(0, 0, 32, 33));
    test!(downcast, Group, I32, Private, count_is!(0, 0, 32, 33));
    test!(downcast_lossy, Group, I32, Constant, count_is!(253, 0, 0, 0));
    test!(downcast_lossy, Group, I32, Public, count_is!(0, 0, 505, 507));

    // Downcast from Group to I64
    test!(downcast, Group, I64, Constant, count_is!(0, 0, 0, 0));
    test!(downcast, Group, I64, Public, count_is!(0, 0, 64, 65));
    test!(downcast, Group, I64, Private, count_is!(0, 0, 64, 65));
    test!(downcast_lossy, Group, I64, Constant, count_is!(253, 0, 0, 0));
    test!(downcast_lossy, Group, I64, Public, count_is!(0, 0, 505, 507));
    test!(downcast_lossy, Group, I64, Private, count_is!(0, 0, 505, 507));

    // Downcast from Group to I128
    test!(downcast, Group, I128, Constant, count_is!(0, 0, 0, 0));
    test!(downcast, Group, I128, Public, count_is!(0, 0, 128, 129));
    test!(downcast, Group, I128, Private, count_is!(0, 0, 128, 129));
    test!(downcast_lossy, Group, I128, Constant, count_is!(253, 0, 0, 0));
    test!(downcast_lossy, Group, I128, Public, count_is!(0, 0, 505, 507));
    test!(downcast_lossy, Group, I128, Private, count_is!(0, 0, 505, 507));

    // Downcast from Group to U8
    test!(downcast, Group, U8, Constant, count_is!(0, 0, 0, 0));
    test!(downcast, Group, U8, Public, count_is!(0, 0, 8, 9));
    test!(downcast, Group, U8, Private, count_is!(0, 0, 8, 9));
    test!(downcast_lossy, Group, U8, Constant, count_is!(253, 0, 0, 0));
    test!(downcast_lossy, Group, U8, Public, count_is!(0, 0, 505, 507));
    test!(downcast_lossy, Group, U8, Private, count_is!(0, 0, 505, 507));

    // Downcast from Group to U16
    test!(downcast, Group, U16, Constant, count_is!(0, 0, 0, 0));
    test!(downcast, Group, U16, Public, count_is!(0, 0, 16, 17));
    test!(downcast, Group, U16, Private, count_is!(0, 0, 16, 17));
    test!(downcast_lossy, Group, U16, Constant, count_is!(253, 0, 0, 0));
    test!(downcast_lossy, Group, U16, Public, count_is!(0, 0, 505, 507));
    test!(downcast_lossy, Group, U16, Private, count_is!(0, 0, 505, 507));

    // Downcast from Group to U32
    test!(downcast, Group, U32, Constant, count_is!(0, 0, 0, 0));
    test!(downcast, Group, U32, Public, count_is!(0, 0, 32, 33));
    test!(downcast, Group, U32, Private, count_is!(0, 0, 32, 33));
    test!(downcast_lossy, Group, U32, Constant, count_is!(253, 0, 0, 0));
    test!(downcast_lossy, Group, U32, Public, count_is!(0, 0, 505, 507));

    // Downcast from Group to U64
    test!(downcast, Group, U64, Constant, count_is!(0, 0, 0, 0));
    test!(downcast, Group, U64, Public, count_is!(0, 0, 64, 65));
    test!(downcast, Group, U64, Private, count_is!(0, 0, 64, 65));
    test!(downcast_lossy, Group, U64, Constant, count_is!(253, 0, 0, 0));
    test!(downcast_lossy, Group, U64, Public, count_is!(0, 0, 505, 507));
    test!(downcast_lossy, Group, U64, Private, count_is!(0, 0, 505, 507));

    // Downcast from Group to U128
    test!(downcast, Group, U128, Constant, count_is!(0, 0, 0, 0));
    test!(downcast, Group, U128, Public, count_is!(0, 0, 128, 129));
    test!(downcast, Group, U128, Private, count_is!(0, 0, 128, 129));
    test!(downcast_lossy, Group, U128, Constant, count_is!(253, 0, 0, 0));
    test!(downcast_lossy, Group, U128, Public, count_is!(0, 0, 505, 507));
    test!(downcast_lossy, Group, U128, Private, count_is!(0, 0, 505, 507));

    // Downcast from Group to Scalar
    test!(downcast, Group, Scalar, Constant, count_is!(253, 0, 0, 0));
    test!(downcast, Group, Scalar, Public, count_is!(0, 0, 755, 760));
    test!(downcast, Group, Scalar, Private, count_is!(0, 0, 755, 760));
    test!(downcast_lossy, Group, Scalar, Constant, count_is!(253, 0, 0, 0));
    test!(downcast_lossy, Group, Scalar, Public, count_is!(0, 0, 505, 507));
    test!(downcast_lossy, Group, Scalar, Private, count_is!(0, 0, 505, 507));

    // TODO: Downcast from Field to Boolean.

    // Downcast from Field to Field.
    test!(downcast, Field, Field, Constant, count_is!(0, 0, 0, 0));
    test!(downcast, Field, Field, Public, count_is!(0, 0, 0, 0));
    test!(downcast, Field, Field, Private, count_is!(0, 0, 0, 0));
    test!(downcast_lossy, Field, Field, Constant, count_is!(0, 0, 0, 0));
    test!(downcast_lossy, Field, Field, Public, count_is!(0, 0, 0, 0));
    test!(downcast_lossy, Field, Field, Private, count_is!(0, 0, 0, 0));

    // Downcast from Field to I8
    test!(downcast, Field, I8, Constant, count_is!(0, 0, 0, 0));
    test!(downcast, Field, I8, Public, count_is!(0, 0, 8, 9));
    test!(downcast, Field, I8, Private, count_is!(0, 0, 8, 9));
    test!(downcast_lossy, Field, I8, Constant, count_is!(253, 0, 0, 0));
    test!(downcast_lossy, Field, I8, Public, count_is!(0, 0, 505, 507));
    test!(downcast_lossy, Field, I8, Private, count_is!(0, 0, 505, 507));

    // Downcast from Field to I16
    test!(downcast, Field, I16, Constant, count_is!(0, 0, 0, 0));
    test!(downcast, Field, I16, Public, count_is!(0, 0, 16, 17));
    test!(downcast, Field, I16, Private, count_is!(0, 0, 16, 17));
    test!(downcast_lossy, Field, I16, Constant, count_is!(253, 0, 0, 0));
    test!(downcast_lossy, Field, I16, Public, count_is!(0, 0, 505, 507));
    test!(downcast_lossy, Field, I16, Private, count_is!(0, 0, 505, 507));

    // Downcast from Field to I32
    test!(downcast, Field, I32, Constant, count_is!(0, 0, 0, 0));
    test!(downcast, Field, I32, Public, count_is!(0, 0, 32, 33));
    test!(downcast, Field, I32, Private, count_is!(0, 0, 32, 33));
    test!(downcast_lossy, Field, I32, Constant, count_is!(253, 0, 0, 0));
    test!(downcast_lossy, Field, I32, Public, count_is!(0, 0, 505, 507));

    // Downcast from Field to I64
    test!(downcast, Field, I64, Constant, count_is!(0, 0, 0, 0));
    test!(downcast, Field, I64, Public, count_is!(0, 0, 64, 65));
    test!(downcast, Field, I64, Private, count_is!(0, 0, 64, 65));
    test!(downcast_lossy, Field, I64, Constant, count_is!(253, 0, 0, 0));
    test!(downcast_lossy, Field, I64, Public, count_is!(0, 0, 505, 507));
    test!(downcast_lossy, Field, I64, Private, count_is!(0, 0, 505, 507));

    // Downcast from Field to I128
    test!(downcast, Field, I128, Constant, count_is!(0, 0, 0, 0));
    test!(downcast, Field, I128, Public, count_is!(0, 0, 128, 129));
    test!(downcast, Field, I128, Private, count_is!(0, 0, 128, 129));
    test!(downcast_lossy, Field, I128, Constant, count_is!(253, 0, 0, 0));
    test!(downcast_lossy, Field, I128, Public, count_is!(0, 0, 505, 507));
    test!(downcast_lossy, Field, I128, Private, count_is!(0, 0, 505, 507));

    // Downcast from Field to U8
    test!(downcast, Field, U8, Constant, count_is!(0, 0, 0, 0));
    test!(downcast, Field, U8, Public, count_is!(0, 0, 8, 9));
    test!(downcast, Field, U8, Private, count_is!(0, 0, 8, 9));
    test!(downcast_lossy, Field, U8, Constant, count_is!(253, 0, 0, 0));
    test!(downcast_lossy, Field, U8, Public, count_is!(0, 0, 505, 507));
    test!(downcast_lossy, Field, U8, Private, count_is!(0, 0, 505, 507));

    // Downcast from Field to U16
    test!(downcast, Field, U16, Constant, count_is!(0, 0, 0, 0));
    test!(downcast, Field, U16, Public, count_is!(0, 0, 16, 17));
    test!(downcast, Field, U16, Private, count_is!(0, 0, 16, 17));
    test!(downcast_lossy, Field, U16, Constant, count_is!(253, 0, 0, 0));
    test!(downcast_lossy, Field, U16, Public, count_is!(0, 0, 505, 507));
    test!(downcast_lossy, Field, U16, Private, count_is!(0, 0, 505, 507));

    // Downcast from Field to U32
    test!(downcast, Field, U32, Constant, count_is!(0, 0, 0, 0));
    test!(downcast, Field, U32, Public, count_is!(0, 0, 32, 33));
    test!(downcast, Field, U32, Private, count_is!(0, 0, 32, 33));
    test!(downcast_lossy, Field, U32, Constant, count_is!(253, 0, 0, 0));
    test!(downcast_lossy, Field, U32, Public, count_is!(0, 0, 505, 507));

    // Downcast from Field to U64
    test!(downcast, Field, U64, Constant, count_is!(0, 0, 0, 0));
    test!(downcast, Field, U64, Public, count_is!(0, 0, 64, 65));
    test!(downcast, Field, U64, Private, count_is!(0, 0, 64, 65));
    test!(downcast_lossy, Field, U64, Constant, count_is!(253, 0, 0, 0));
    test!(downcast_lossy, Field, U64, Public, count_is!(0, 0, 505, 507));
    test!(downcast_lossy, Field, U64, Private, count_is!(0, 0, 505, 507));

    // Downcast from Field to U128
    test!(downcast, Field, U128, Constant, count_is!(0, 0, 0, 0));
    test!(downcast, Field, U128, Public, count_is!(0, 0, 128, 129));
    test!(downcast, Field, U128, Private, count_is!(0, 0, 128, 129));
    test!(downcast_lossy, Field, U128, Constant, count_is!(253, 0, 0, 0));
    test!(downcast_lossy, Field, U128, Public, count_is!(0, 0, 505, 507));
    test!(downcast_lossy, Field, U128, Private, count_is!(0, 0, 505, 507));

    // Downcast from Field to Scalar
    test!(downcast, Field, Scalar, Constant, count_is!(253, 0, 0, 0));
    test!(downcast, Field, Scalar, Public, count_is!(0, 0, 755, 760));
    test!(downcast, Field, Scalar, Private, count_is!(0, 0, 755, 760));
    test!(downcast_lossy, Field, Scalar, Constant, count_is!(253, 0, 0, 0));
    test!(downcast_lossy, Field, Scalar, Public, count_is!(0, 0, 505, 507));
    test!(downcast_lossy, Field, Scalar, Private, count_is!(0, 0, 505, 507));
}
