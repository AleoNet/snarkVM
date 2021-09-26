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

pub mod boolean;
pub mod field;
pub mod traits;

use snarkvm_curves::bls12_377::Fr;
use snarkvm_fields::PrimeField;

use once_cell::unsync::OnceCell;
use std::{
    cell::{Ref, RefCell},
    rc::Rc,
};

pub trait Environment {
    type Field: PrimeField + Copy;

    fn scope(name: &str) -> CircuitSpan<Self::Field>;

    // fn scoped<'a, EE, F>(name: &str, logic: F)
    // where
    //     EE: 'a + Environment,
    //     F: FnOnce(CircuitScope<'a, EE>) -> ();

    // fn scope<E, F>(name: &str, logic: F)
    // where
    //     E: Environment<Field = Fr>,
    //     F: FnOnce(E) -> ();

    fn one() -> Variable<Self::Field>;

    fn new_constant(value: Self::Field) -> Variable<Self::Field>;
    fn new_public(value: Self::Field) -> Variable<Self::Field>;
    fn new_private(value: Self::Field) -> Variable<Self::Field>;

    fn num_constants() -> usize;
    fn num_public() -> usize;
    fn num_private() -> usize;
    fn num_constraints() -> usize;
}

thread_local! {
    static CB: OnceCell<RefCell<CircuitBuilder>> = OnceCell::new();
}

pub type Scope = String;

#[derive(Clone)]
pub struct CircuitBuilder(CircuitSpan<Fr>);

impl CircuitBuilder {
    fn cs() -> CircuitSpan<<Self as Environment>::Field> {
        CB.with(|cb| {
            cb.get_or_init(|| {
                let circuit = Rc::new(RefCell::new(Circuit::new()));
                let builder = CircuitBuilder(CircuitSpan::<<Self as Environment>::Field>::new(
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

    fn scope(name: &str) -> CircuitSpan<Self::Field> {
        CB.with(|cb| {
            let span = cb.get().unwrap().borrow().0.clone().scope(name);
            (*cb.get().unwrap().borrow_mut()).0 = span.clone();
            span
        })
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

    fn one() -> Variable<Self::Field> {
        Self::cs().one()
    }

    fn new_constant(value: Self::Field) -> Variable<Self::Field> {
        Self::cs().new_constant(value)
    }

    fn new_public(value: Self::Field) -> Variable<Self::Field> {
        Self::cs().new_public(value)
    }

    fn new_private(value: Self::Field) -> Variable<Self::Field> {
        Self::cs().new_private(value)
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
//         println!("I AM IN DROP {:?} {:?}", self.0.scope, self.0.previous);
//         if let Some(scope) = &self.0.previous {
//             println!("I AM DROPPING {:?} {:?}", self.0.scope, self.0.previous);
//
//             // self.scope = (*scope).clone();
//
//             // CB.with(|cb| {
//             //     (*cb.get().unwrap().borrow_mut()).0.scope = (*scope).clone();
//             //     // (*cb.get().unwrap().borrow_mut()).0.scope = (*scope).clone();
//             // });
//         }
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

#[derive(Clone)]
pub struct CircuitSpan<F: PrimeField> {
    circuit: Rc<RefCell<Circuit<F>>>,
    scope: Scope,
    previous: Option<Scope>,
}

impl<F: PrimeField> CircuitSpan<F> {
    fn new(circuit: Rc<RefCell<Circuit<F>>>, scope: Scope, previous: Option<Scope>) -> Self {
        Self {
            circuit,
            scope,
            previous,
        }
    }

    fn scope(self, name: &str) -> Self {
        Self {
            circuit: self.circuit.clone(),
            scope: format!("{}/{}", self.scope, name),
            previous: Some(self.scope.clone()),
        }
    }

    fn one(&self) -> Variable<F> {
        self.circuit.borrow().one()
    }

    fn new_constant(&mut self, value: F) -> Variable<F> {
        self.circuit.borrow_mut().new_constant(value, self.scope.clone())
    }

    fn new_public(&mut self, value: F) -> Variable<F> {
        self.circuit.borrow_mut().new_public(value, self.scope.clone())
    }

    fn new_private(&mut self, value: F) -> Variable<F> {
        self.circuit.borrow_mut().new_private(value, self.scope.clone())
    }

    fn num_constants(&self) -> usize {
        self.circuit.borrow().num_constants()
    }

    fn num_public(&self) -> usize {
        self.circuit.borrow().num_public()
    }

    fn num_private(&self) -> usize {
        self.circuit.borrow().num_private()
    }

    fn num_constraints(&self) -> usize {
        self.circuit.borrow().num_constraints()
    }

    fn num_constants_in_scope(&self) -> usize {
        self.circuit.borrow().num_constants_in_scope(&self.scope)
    }

    fn num_public_in_scope(&self) -> usize {
        self.circuit.borrow().num_public_in_scope(&self.scope)
    }

    fn num_private_in_scope(&self) -> usize {
        self.circuit.borrow().num_private_in_scope(&self.scope)
    }

    fn num_constraints_in_scope(&self) -> usize {
        self.circuit.borrow().num_constraints_in_scope(&self.scope)
    }
}

// impl<F: PrimeField> Drop for CircuitSpan<F> {
//     #[inline]
//     fn drop(&mut self) {
//         println!("I AM IN DROP {:?} {:?}", self.scope, self.previous);
//         if let Some(scope) = &self.previous {
//             println!("I AM DROPPING {:?} {:?}", self.scope, self.previous);
//
//             let prev = (*self).circuit.borrow_mut().pop_scope();
//             (*self).scope = (prev).clone();
//             (*self).previous = None;
//
//             // CB.with(|cb| {
//             //     (*cb.get().unwrap().borrow_mut()).0.scope = (*scope).clone();
//             //     // (*cb.get().unwrap().borrow_mut()).0.scope = (*scope).clone();
//             // });
//         }
//     }
// }

pub enum Mode {
    Constant,
    Public,
    Private,
}

pub type Index = u64;

use std::ops::Add;

use std::collections::{HashMap, HashSet};

#[derive(Clone, Debug)]
pub struct LinearCombination<F: PrimeField>(HashMap<Variable<F>, F>);

impl<F: PrimeField> LinearCombination<F> {
    fn to_value(&self) -> F {
        let mut result = F::zero();

        for (variable, coefficient) in self.0.iter() {
            let value = match variable {
                Variable::Constant(value) => value,
                Variable::Public(_, value) => value,
                Variable::Private(_, value) => value,
            };

            result += *value * coefficient;
        }

        result
    }
}

impl<F: PrimeField> From<Variable<F>> for LinearCombination<F> {
    fn from(variable: Variable<F>) -> Self {
        Self([(variable, F::one())].iter().cloned().collect())
    }
}

impl<F: PrimeField, const N: usize> From<[Variable<F>; N]> for LinearCombination<F> {
    fn from(variables: [Variable<F>; N]) -> Self {
        Self::from(&variables[..])
    }
}

impl<F: PrimeField, const N: usize> From<&[Variable<F>; N]> for LinearCombination<F> {
    fn from(variables: &[Variable<F>; N]) -> Self {
        Self::from(&variables[..])
    }
}

impl<F: PrimeField> From<Vec<Variable<F>>> for LinearCombination<F> {
    fn from(variables: Vec<Variable<F>>) -> Self {
        Self::from(variables.as_slice())
    }
}

impl<F: PrimeField> From<&Vec<Variable<F>>> for LinearCombination<F> {
    fn from(variables: &Vec<Variable<F>>) -> Self {
        Self::from(variables.as_slice())
    }
}

impl<F: PrimeField> From<&[Variable<F>]> for LinearCombination<F> {
    fn from(variables: &[Variable<F>]) -> Self {
        let mut combination = HashMap::with_capacity(variables.len());
        for variable in variables {
            match combination.get_mut(variable) {
                Some(coefficient) => *coefficient += F::one(),
                None => {
                    combination.insert(*variable, F::one());
                }
            }
        }
        Self(combination)
    }
}

impl<F: PrimeField> Add<LinearCombination<F>> for LinearCombination<F> {
    type Output = Self;

    fn add(self, other: Self) -> Self::Output {
        let mut combination = self.0;
        for (variable, other_coefficient) in other.0.iter() {
            match combination.get_mut(variable) {
                Some(coefficient) => *coefficient += *other_coefficient,
                None => {
                    combination.insert(*variable, *other_coefficient);
                }
            }
        }
        Self(combination)
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Variable<F: PrimeField> {
    Constant(F),
    Public(Index, F),
    Private(Index, F),
}

impl<F: PrimeField> Add<Self> for Variable<F> {
    type Output = LinearCombination<F>;

    fn add(self, other: Self) -> Self::Output {
        match (self, other) {
            (Self::Constant(a), Self::Constant(b)) => Self::Constant(a + b).into(),
            (first, second) => LinearCombination::from([first, second]),
        }
    }
}

#[derive(Debug, Default)]
pub struct CircuitCounter {
    constants: HashMap<Scope, usize>,
    public: HashMap<Scope, usize>,
    private: HashMap<Scope, usize>,
    constraints: HashMap<Scope, usize>,
}

impl CircuitCounter {
    fn increment_constant(&mut self, scope: &Scope) {
        match self.constants.get_mut(scope) {
            Some(counter) => *counter += 1,
            None => assert!(self.constants.insert(scope.clone(), 1).is_none()),
        }
    }

    fn increment_public(&mut self, scope: &Scope) {
        match self.public.get_mut(scope) {
            Some(counter) => *counter += 1,
            None => assert!(self.public.insert(scope.clone(), 1).is_none()),
        }
    }

    fn increment_private(&mut self, scope: &Scope) {
        match self.private.get_mut(scope) {
            Some(counter) => *counter += 1,
            None => assert!(self.private.insert(scope.clone(), 1).is_none()),
        }
    }

    fn increment_constraints(&mut self, scope: &Scope) {
        match self.constraints.get_mut(scope) {
            Some(counter) => *counter += 1,
            None => assert!(self.constraints.insert(scope.clone(), 1).is_none()),
        }
    }

    fn num_constants_in_scope(&self, scope: &Scope) -> usize {
        match self.constants.get(scope) {
            Some(counter) => *counter,
            None => 0,
        }
    }

    fn num_public_in_scope(&self, scope: &Scope) -> usize {
        match self.public.get(scope) {
            Some(counter) => *counter,
            None => 0,
        }
    }

    fn num_private_in_scope(&self, scope: &Scope) -> usize {
        match self.private.get(scope) {
            Some(counter) => *counter,
            None => 0,
        }
    }

    fn num_constraints_in_scope(&self, scope: &Scope) -> usize {
        match self.constraints.get(scope) {
            Some(counter) => *counter,
            None => 0,
        }
    }
}

#[derive(Debug)]
pub struct Circuit<F: PrimeField> {
    constants: Vec<Variable<F>>,
    public: Vec<Variable<F>>,
    private: Vec<Variable<F>>,
    constraints: HashMap<(LinearCombination<F>, LinearCombination<F>, LinearCombination<F>), Scope>,
    transcript: HashMap<Variable<F>, Scope>,
    counter: CircuitCounter,
}

impl<F: PrimeField> Circuit<F> {
    fn new() -> Self {
        Self {
            constants: Default::default(),
            public: vec![Variable::Public(0u64, F::one())],
            private: Default::default(),
            constraints: Default::default(),
            transcript: Default::default(),
            counter: Default::default(),
        }
    }

    /// Return the "one" input variable.
    pub fn one(&self) -> Variable<F> {
        self.public[0]
    }

    pub(crate) fn new_constant(&mut self, value: F, scope: Scope) -> Variable<F> {
        let variable = Variable::Constant(value);
        self.constants.push(variable);
        self.counter.increment_constant(&scope);
        self.transcript.insert(variable, scope);
        variable
    }

    pub(crate) fn new_public(&mut self, value: F, scope: Scope) -> Variable<F> {
        let variable = Variable::Public(self.public.len() as u64, value);
        self.public.push(variable);
        self.counter.increment_public(&scope);
        self.transcript.insert(variable, scope);
        variable
    }

    pub(crate) fn new_private(&mut self, value: F, scope: Scope) -> Variable<F> {
        let variable = Variable::Private(self.private.len() as u64, value);
        self.private.push(variable);
        self.counter.increment_private(&scope);
        self.transcript.insert(variable, scope);
        variable
    }

    fn num_constants(&self) -> usize {
        self.constants.len()
    }

    fn num_public(&self) -> usize {
        self.public.len()
    }

    fn num_private(&self) -> usize {
        self.private.len()
    }

    fn num_constraints(&self) -> usize {
        self.constraints.len()
    }

    fn num_constants_in_scope(&self, scope: &Scope) -> usize {
        self.counter.num_constants_in_scope(scope)
    }

    fn num_public_in_scope(&self, scope: &Scope) -> usize {
        self.counter.num_public_in_scope(scope)
    }

    fn num_private_in_scope(&self, scope: &Scope) -> usize {
        self.counter.num_private_in_scope(scope)
    }

    fn num_constraints_in_scope(&self, scope: &Scope) -> usize {
        self.counter.num_constraints_in_scope(scope)
    }
}
