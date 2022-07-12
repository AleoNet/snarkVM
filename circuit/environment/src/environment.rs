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

use crate::{Assignment, Inject, LinearCombination, Mode, Variable, R1CS};
use snarkvm_curves::{AffineCurve, MontgomeryParameters, TwistedEdwardsParameters};
use snarkvm_fields::traits::*;

use core::{fmt, hash};

pub trait Environment: 'static + Copy + Clone + fmt::Debug + fmt::Display + Eq + PartialEq + hash::Hash {
    type Network: console::Network<Affine = Self::Affine, Field = Self::BaseField, Scalar = Self::ScalarField>;

    type Affine: AffineCurve<
        BaseField = Self::BaseField,
        ScalarField = Self::ScalarField,
        Coordinates = (Self::BaseField, Self::BaseField),
    >;
    type AffineParameters: TwistedEdwardsParameters<BaseField = Self::BaseField>
        + MontgomeryParameters<BaseField = Self::BaseField>;
    type BaseField: PrimeField + SquareRootField + Copy;
    type ScalarField: PrimeField<BigInteger = <Self::BaseField as PrimeField>::BigInteger> + Copy;

    /// The maximum number of bytes allowed in a string.
    const NUM_STRING_BYTES: u32;

    /// Returns the `zero` constant.
    fn zero() -> LinearCombination<Self::BaseField>;

    /// Returns the `one` constant.
    fn one() -> LinearCombination<Self::BaseField>;

    /// Returns a new variable of the given mode and value.
    fn new_variable(mode: Mode, value: Self::BaseField) -> Variable<Self::BaseField>;

    /// Returns a new witness of the given mode and value.
    fn new_witness<Fn: FnOnce() -> Output::Primitive, Output: Inject>(mode: Mode, value: Fn) -> Output;

    /// Enters a new scope for the environment.
    fn scope<S: Into<String>, Fn, Output>(name: S, logic: Fn) -> Output
    where
        Fn: FnOnce() -> Output;

    /// Adds one constraint enforcing that `(A * B) == C`.
    fn enforce<Fn, A, B, C>(constraint: Fn)
    where
        Fn: FnOnce() -> (A, B, C),
        A: Into<LinearCombination<Self::BaseField>>,
        B: Into<LinearCombination<Self::BaseField>>,
        C: Into<LinearCombination<Self::BaseField>>;

    /// Adds one constraint enforcing that the given boolean is `true`.
    fn assert<Boolean: Into<LinearCombination<Self::BaseField>>>(boolean: Boolean) {
        Self::enforce(|| (boolean, Self::one(), Self::one()))
    }

    /// Adds one constraint enforcing that the `A == B`.
    fn assert_eq<A, B>(a: A, b: B)
    where
        A: Into<LinearCombination<Self::BaseField>>,
        B: Into<LinearCombination<Self::BaseField>>,
    {
        Self::enforce(|| (a, Self::one(), b))
    }

    /// Returns `true` if all constraints in the environment are satisfied.
    fn is_satisfied() -> bool;

    /// Returns `true` if all constraints in the current scope are satisfied.
    fn is_satisfied_in_scope() -> bool;

    /// Returns the number of constants in the entire environment.
    fn num_constants() -> u64;

    /// Returns the number of public variables in the entire environment.
    fn num_public() -> u64;

    /// Returns the number of private variables in the entire environment.
    fn num_private() -> u64;

    /// Returns the number of constraints in the entire environment.
    fn num_constraints() -> u64;

    /// Returns the number of gates in the entire environment.
    fn num_gates() -> u64;

    /// Returns a tuple containing the number of constants, public variables, private variables, constraints, and gates in the entire environment.
    fn count() -> (u64, u64, u64, u64, u64) {
        (Self::num_constants(), Self::num_public(), Self::num_private(), Self::num_constraints(), Self::num_gates())
    }

    /// Returns the number of constants for the current scope.
    fn num_constants_in_scope() -> u64;

    /// Returns the number of public variables for the current scope.
    fn num_public_in_scope() -> u64;

    /// Returns the number of private variables for the current scope.
    fn num_private_in_scope() -> u64;

    /// Returns the number of constraints for the current scope.
    fn num_constraints_in_scope() -> u64;

    /// Returns the number of gates for the current scope.
    fn num_gates_in_scope() -> u64;

    /// Returns a tuple containing the number of constants, public variables, private variables, constraints, and gates for the current scope.
    fn count_in_scope() -> (u64, u64, u64, u64, u64) {
        (
            Self::num_constants_in_scope(),
            Self::num_public_in_scope(),
            Self::num_private_in_scope(),
            Self::num_constraints_in_scope(),
            Self::num_gates_in_scope(),
        )
    }

    /// Halts the program from further synthesis, evaluation, and execution in the current environment.
    fn halt<S: Into<String>, T>(message: S) -> T {
        <Self::Network as console::Environment>::halt(message)
    }

    /// Returns the R1CS circuit, resetting the circuit.
    fn inject_r1cs(r1cs: R1CS<Self::BaseField>);

    /// Returns the R1CS circuit, resetting the circuit.
    fn eject_r1cs_and_reset() -> R1CS<Self::BaseField>;

    /// Returns the R1CS assignment of the circuit, resetting the circuit.
    fn eject_assignment_and_reset() -> Assignment<Self::BaseField>;

    /// Clears and initializes an empty environment.
    fn reset();
}
