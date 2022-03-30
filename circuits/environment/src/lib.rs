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
#![allow(clippy::type_complexity)]

#[macro_use]
extern crate num_derive;

extern crate snarkvm_circuits_environment_witness;
pub use snarkvm_circuits_environment_witness::rename_selfs;

pub mod circuit;
pub use circuit::*;

pub mod environment;
pub use environment::*;

pub mod helpers;
pub use helpers::*;

pub mod macros;
pub use macros::*;

pub mod traits;
pub use traits::*;

pub mod prelude {
    pub use crate::{rename_selfs, traits::*, witness, witness_mode, Environment, LinearCombination, Mode, Variable};
    pub use snarkvm_fields::{Field as F, One as O, PrimeField, Zero as Z};

    pub use core::{
        fmt::{self, Debug, Display},
        ops::{
            Add,
            AddAssign,
            BitAnd,
            BitAndAssign,
            BitOr,
            BitOrAssign,
            BitXor,
            BitXorAssign,
            Div,
            DivAssign,
            Mul,
            MulAssign,
            Neg,
            Not,
            Shl,
            ShlAssign,
            Shr,
            ShrAssign,
            Sub,
            SubAssign,
        },
    };
    pub use itertools::Itertools;
    pub use nom::{
        branch::alt,
        bytes::complete::tag,
        character::complete::{char, one_of},
        combinator::{map, map_res, opt, recognize},
        multi::{many0, many1},
        sequence::{pair, terminated},
    };
    pub use num_traits::{Inv, One as NumOne, Pow, Unsigned};
    pub use once_cell::unsync::OnceCell;
}

#[cfg(test)]
pub use test_utilities::*;
pub mod test_utilities {
    use super::*;
    use core::{
        fmt::{Debug, Display},
        panic::UnwindSafe,
    };

    // Dev Note: We instantiate the environment as `Circuit` since it saves us from having to specify
    // a large number of type annotations in our tests. If more than one implementor of `Environment`
    // exists, then we must make this generic over the `Environment` trait.

    pub fn check_operation_passes<V: Debug + Display + PartialEq, LHS, RHS, OUT: Eject<Primitive = V>>(
        name: &str,
        case: &str,
        expected: V,
        a: LHS,
        b: RHS,
        operation: impl FnOnce(LHS, RHS) -> OUT,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        Circuit::scope(name, || {
            let candidate = operation(a, b);
            assert_eq!(expected, candidate.eject_value(), "{} != {} := {}", expected, candidate.eject_value(), case);
            assert_scope!(case, num_constants, num_public, num_private, num_constraints);
        });
        Circuit::reset();
    }

    pub fn check_operation_passes_without_counts<
        V: Debug + Display + PartialEq,
        LHS,
        RHS,
        OUT: Eject<Primitive = V>,
    >(
        name: &str,
        case: &str,
        expected: V,
        a: LHS,
        b: RHS,
        operation: impl FnOnce(LHS, RHS) -> OUT,
    ) {
        Circuit::scope(name, || {
            let candidate = operation(a, b);
            assert_eq!(expected, candidate.eject_value(), "{} != {} := {}", expected, candidate.eject_value(), case);
        });
        Circuit::reset();
    }

    pub fn check_operation_fails<LHS, RHS, OUT>(
        name: &str,
        case: &str,
        a: LHS,
        b: RHS,
        operation: impl FnOnce(LHS, RHS) -> OUT,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        Circuit::scope(name, || {
            let _candidate = operation(a, b);
            assert_scope_fails!(case, num_constants, num_public, num_private, num_constraints);
        });
        Circuit::reset();
    }

    pub fn check_operation_fails_without_counts<LHS, RHS, OUT>(
        name: &str,
        case: &str,
        a: LHS,
        b: RHS,
        operation: impl FnOnce(LHS, RHS) -> OUT,
    ) {
        Circuit::scope(name, || {
            let _candidate = operation(a, b);
            assert!(!Circuit::is_satisfied(), "{} (!is_satisfied)", case);
        });
        Circuit::reset();
    }

    pub fn check_operation_halts<LHS: UnwindSafe, RHS: UnwindSafe, OUT>(
        a: LHS,
        b: RHS,
        operation: impl FnOnce(LHS, RHS) -> OUT + UnwindSafe,
    ) {
        let result = std::panic::catch_unwind(|| operation(a, b));
        assert!(result.is_err());
    }

    pub fn check_unary_operation_passes<V: Debug + Display + PartialEq, IN, OUT: Eject<Primitive = V>>(
        name: &str,
        case: &str,
        expected: V,
        input: IN,
        operation: impl FnOnce(IN) -> OUT,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        Circuit::scope(name, || {
            let candidate = operation(input);
            assert_eq!(expected, candidate.eject_value(), "{}", case);
            assert_scope!(case, num_constants, num_public, num_private, num_constraints);
        });
        Circuit::reset();
    }

    pub fn check_unary_operation_fails<IN, OUT>(
        name: &str,
        case: &str,
        input: IN,
        operation: impl FnOnce(IN) -> OUT,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        Circuit::scope(name, || {
            let _candidate = operation(input);
            assert_scope_fails!(case, num_constants, num_public, num_private, num_constraints);
        });
        Circuit::reset();
    }

    pub fn check_unary_operation_fails_without_counts<IN, OUT>(
        name: &str,
        case: &str,
        input: IN,
        operation: impl FnOnce(IN) -> OUT,
    ) {
        Circuit::scope(name, || {
            let _candidate = operation(input);
            assert!(!Circuit::is_satisfied(), "{} (!is_satisfied)", case);
        });
        Circuit::reset();
    }

    pub fn check_unary_operation_halts<IN: UnwindSafe, OUT>(input: IN, operation: impl FnOnce(IN) -> OUT + UnwindSafe) {
        let result = std::panic::catch_unwind(|| operation(input));
        assert!(result.is_err());
    }
}
