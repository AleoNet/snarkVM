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

use crate::{Metric, MetricForOperation};

use snarkvm_circuits_environment::{AddWrapped, Eject, Environment, IntegerType, Mode};
use snarkvm_circuits_types::integers::Integer;

impl<E: Environment, I: IntegerType> MetricForOperation for dyn AddWrapped<Integer<E, I>, Output = Integer<E, I>> {
    type Input = (Integer<E, I>, Integer<E, I>);
    type Metric = (Metric<usize>, Metric<usize>, Metric<usize>, Metric<usize>);

    fn get_metric(input: &Self::Input) -> Self::Metric {
        let (lhs, rhs) = input;
        match (lhs.eject_mode(), rhs.eject_mode()) {
            (Mode::Constant, Mode::Constant) => {
                (Metric::equal(I::BITS), Metric::equal(0), Metric::equal(0), Metric::equal(0))
            }
            (Mode::Constant, Mode::Public)
            | (Mode::Constant, Mode::Private)
            | (Mode::Public, Mode::Constant)
            | (Mode::Private, Mode::Constant)
            | (Mode::Public, Mode::Public)
            | (Mode::Public, Mode::Private)
            | (Mode::Private, Mode::Public)
            | (Mode::Private, Mode::Private) => {
                (Metric::equal(0), Metric::equal(0), Metric::equal(I::BITS + 1), Metric::equal(I::BITS + 2))
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use snarkvm_circuits_environment::{Circuit, Inject, Operation};

    #[test]
    fn test_add_wrapped_metrics() {
        type I = u8;
        let inputs = (Integer::<Circuit, I>::new(Mode::Private, 1), Integer::<Circuit, I>::new(Mode::Private, 2));
        let (num_constants, num_public, num_private, num_constraints) =
            <dyn AddWrapped<Integer<Circuit, I>, Output = Integer<Circuit, I>> as MetricForOperation>::get_metric(
                &inputs,
            );
        Circuit::scope("AddWrapped", || {
            <dyn AddWrapped<Integer<Circuit, I>, Output = Integer<Circuit, I>> as Operation<Integer<Circuit, I>>>::invoke(inputs);
            num_constants.is_satisfied(Circuit::num_constants_in_scope());
            num_public.is_satisfied(Circuit::num_public_in_scope());
            num_private.is_satisfied(Circuit::num_private_in_scope());
            num_constraints.is_satisfied(Circuit::num_constraints_in_scope());
        })
    }
}
