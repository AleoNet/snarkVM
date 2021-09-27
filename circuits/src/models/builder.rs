// Copyright (C) 2019-2021 Aleo Systems Inc.
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

use crate::{models::*, traits::*};

use snarkvm_curves::bls12_377::Fr;
use snarkvm_fields::PrimeField;

use once_cell::unsync::OnceCell;
use std::{
    cell::{Ref, RefCell},
    rc::Rc,
};

thread_local! {
    static CB: OnceCell<RefCell<CircuitBuilder>> = OnceCell::new();
}

#[derive(Clone)]
pub struct CircuitBuilder(CircuitScope<Fr>);

impl CircuitBuilder {
    fn cs() -> CircuitScope<<Self as Environment>::Field> {
        CB.with(|cb| {
            cb.get_or_init(|| {
                let circuit = Rc::new(RefCell::new(Circuit::new()));
                let builder = CircuitBuilder(CircuitScope::<<Self as Environment>::Field>::new(
                    circuit,
                    format!("ConstraintSystem::new"),
                    None,
                ));
                RefCell::new(builder)
            })
            .borrow()
            .0
            .clone()
        })
    }

    // fn new_constant(value: Self::Field) -> Variable<Self::Field> {
    //     Self::cs().new_constant(value)
    // }
    //
    // fn new_public(value: Self::Field) -> Variable<Self::Field> {
    //     Self::cs().new_public(value)
    // }
    //
    // fn new_private(value: Self::Field) -> Variable<Self::Field> {
    //     Self::cs().new_private(value)
    // }

    pub fn print_circuit() {
        println!("{:?}", Self::cs().circuit.borrow());
    }
}

impl Environment for CircuitBuilder {
    type Field = Fr;

    // fn span(name: &str) -> CircuitSpan<Self> {
    //     CB.with(|cb| {
    //         let builder = cb.get().unwrap().borrow().0.clone().scope(name);
    //         (*cb.get().unwrap().borrow_mut()).0 = builder;
    //     })
    // }

    fn is_satisfied() -> bool {
        Self::cs().is_satisfied()
    }

    fn scope(name: &str) -> CircuitScope<Self::Field> {
        // CB.with(|cb| {
        //     let span = cb.get().unwrap().borrow().0.clone().scope(name);
        //     (*cb.get().unwrap().borrow_mut()).0 = span.clone();
        //     span
        // })

        CB.with(|cb| {
            let scope = Self::cs().scope(name);
            (*cb.get().unwrap().borrow_mut()).0 = scope.clone();
            scope
        })
    }

    fn scoped<Fn>(name: &str, logic: Fn)
    where
        Fn: FnOnce(CircuitScope<Self::Field>) -> (),
    {
        CB.with(|cb| {
            // Fetch the current environment.
            let current = Self::cs().clone();

            // Set the entire environment to the new scope, and run the logic.
            let scope = current.clone().scope(name);
            (*cb.get().unwrap().borrow_mut()).0 = scope.clone();
            logic(scope);

            // Return the entire environment to the previous scope.
            (*cb.get().unwrap().borrow_mut()).0 = current;
        });
    }

    // fn span(name: &str) -> CircuitSpan<Self> {
    //     Self::cs().scope(name)
    // }

    // fn scope(name: &str) -> CircuitSpan<Self> {
    //     // CB.with(|cb| {
    //     //     let cb = cb.get_mut().unwrap();
    //     //     let new_scope = cb.0.scope(name);
    //     //     cb.0 = new_scope;
    //     //     cb.0.clone()
    //     // })
    //
    //     Self::cs().scope(name)
    // }

    // fn scope<E, F>(name: &str, logic: F)
    // where
    //     E: Environment<Field = Fr>,
    //     F: FnOnce(E) -> (),
    // {
    //     CB.with(|cb| {
    //         // let builder = cb.get().unwrap().borrow().0.clone();
    //
    //         let span = &cb.get().unwrap().borrow().0;
    //         let circuit = span.circuit.clone();
    //         let scope = span.scope.clone();
    //
    //         let span = CircuitSpan::<E>::new(circuit, scope, None);
    //
    //         logic(span.scope(name))
    //     });
    // }

    fn zero() -> LinearCombination<Self::Field> {
        LinearCombination::zero()
    }

    fn one() -> LinearCombination<Self::Field> {
        LinearCombination::one()
    }

    fn new_variable(mode: Mode, value: Self::Field) -> Variable<Self::Field> {
        match mode {
            Mode::Constant => Self::cs().new_constant(value),
            Mode::Public => Self::cs().new_public(value),
            Mode::Private => Self::cs().new_private(value),
        }
    }

    fn enforce<Fn, A, B, C>(constraint: Fn)
    where
        Fn: FnOnce() -> (A, B, C),
        A: Into<LinearCombination<Self::Field>>,
        B: Into<LinearCombination<Self::Field>>,
        C: Into<LinearCombination<Self::Field>>,
    {
        Self::cs().enforce(constraint)
    }

    fn num_constants() -> usize {
        Self::cs().num_constants()
    }

    fn num_public() -> usize {
        Self::cs().num_public()
    }

    fn num_private() -> usize {
        Self::cs().num_private()
    }

    fn num_constraints() -> usize {
        Self::cs().num_constraints()
    }
}

// impl Drop for CircuitBuilder {
//     #[inline]
//     fn drop(&mut self) {
//         println!("I AM IN DROP {:?}", self);
//         // if let Some(scope) = &self.0.previous {
//         //     println!("I AM DROPPING {:?}", self);
//         //
//         //     // self.scope = (*scope).clone();
//         //
//         //     // CB.with(|cb| {
//         //     //     (*cb.get().unwrap().borrow_mut()).0.scope = (*scope).clone();
//         //     //     // (*cb.get().unwrap().borrow_mut()).0.scope = (*scope).clone();
//         //     // });
//         // }
//     }
// }

// impl Drop for CircuitBuilder {
//     /// Pops the scope.
//     #[inline]
//     fn drop(&mut self) {
//         // CB.with(|cb| {
//         //     if let Some(previous_scope) = &cb.get().unwrap().borrow().0 .2 {
//         //         (*cb.get().unwrap().borrow_mut()).0 = (**previous_scope).clone();
//         //     }
//         // });
//     }
// }

// impl Drop for CircuitBuilder {
//     #[inline]
//     fn drop(&mut self) {
//         if let Some(scope) = &self.2 {
//             *self = (**scope).clone();
//         }
//     }
// }
