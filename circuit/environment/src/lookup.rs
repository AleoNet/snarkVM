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

use crate::{
    BaseConstraint,
    Circuit,
    Constraint,
    Environment,
    EnvironmentError,
    LinearCombination,
    Mode,
    Variable,
    CIRCUIT,
    IN_WITNESS,
    LOOKUP_TABLES,
};

use snarkvm_r1cs::LookupTable;

pub trait Lookup: Environment {
    fn add_lookup_table(lookup_table: LookupTable<Self::BaseField>) -> usize;

    fn unary_lookup<A: Into<LinearCombination<Self::BaseField>>>(
        id: usize,
        key: A,
    ) -> Result<(Variable<Self::BaseField>, Variable<Self::BaseField>), EnvironmentError>;

    fn binary_lookup<A: Into<LinearCombination<Self::BaseField>>, B: Into<LinearCombination<Self::BaseField>>>(
        id: usize,
        key_1: A,
        key_2: B,
    ) -> Result<Variable<Self::BaseField>, EnvironmentError>;

    fn index_lookup(
        id: usize,
        index: usize,
    ) -> Result<(Variable<Self::BaseField>, Variable<Self::BaseField>, Variable<Self::BaseField>), EnvironmentError>;

    fn enforce_lookup<Fn, A, B, C>(constraint: Fn)
    where
        Fn: FnOnce() -> (A, B, C),
        A: Into<LinearCombination<Self::BaseField>>,
        B: Into<LinearCombination<Self::BaseField>>,
        C: Into<LinearCombination<Self::BaseField>>;
}

impl Lookup for Circuit {
    fn add_lookup_table(lookup_table: LookupTable<Self::BaseField>) -> usize {
        LOOKUP_TABLES.with(|lookup_tables| {
            let lookup_tables = &mut *(**lookup_tables).borrow_mut();
            lookup_tables.push(lookup_table);
            lookup_tables.len() - 1
        })
    }

    fn unary_lookup<A: Into<LinearCombination<Self::BaseField>>>(
        id: usize,
        key: A,
    ) -> Result<(Variable<Self::BaseField>, Variable<Self::BaseField>), EnvironmentError> {
        let lc = key.into();
        let val = lc.value();
        let (a, b) = LOOKUP_TABLES.with(|lookup_tables| {
            let lookup_tables = &*(**lookup_tables).borrow();
            let table = lookup_tables.get(id).ok_or(EnvironmentError::LookupTableMissing)?;
            if let Some(row) = table.0.iter().find(|row| row.0 == val) {
                Ok((row.1, row.2))
            } else {
                Err(EnvironmentError::LookupValueMissing)
            }
        })?;

        let vars = (Self::new_variable(Mode::Private, a), Self::new_variable(Mode::Private, b));
        Self::enforce_lookup(|| (lc, vars.0.clone(), vars.1.clone()));
        Ok(vars)
    }

    fn binary_lookup<A: Into<LinearCombination<Self::BaseField>>, B: Into<LinearCombination<Self::BaseField>>>(
        id: usize,
        key_1: A,
        key_2: B,
    ) -> Result<Variable<Self::BaseField>, EnvironmentError> {
        let lc_1 = key_1.into();
        let lc_2 = key_2.into();
        let val_1 = lc_1.value();
        let val_2 = lc_2.value();
        let a = LOOKUP_TABLES.with(|lookup_tables| {
            let lookup_tables = &*(**lookup_tables).borrow();
            let table = lookup_tables.get(id).ok_or(EnvironmentError::LookupTableMissing)?;
            if let Some(row) = table.0.iter().find(|row| row.0 == val_1 && row.1 == val_2) {
                Ok(row.2)
            } else {
                Err(EnvironmentError::LookupValueMissing)
            }
        })?;

        let var = Self::new_variable(Mode::Private, a);
        Self::enforce_lookup(|| (lc_1, lc_2, var.clone()));
        Ok(var)
    }

    fn index_lookup(
        id: usize,
        index: usize,
    ) -> Result<(Variable<Self::BaseField>, Variable<Self::BaseField>, Variable<Self::BaseField>), EnvironmentError>
    {
        let (a, b, c) = LOOKUP_TABLES.with(|lookup_tables| {
            let lookup_tables = &*(**lookup_tables).borrow();
            let table = lookup_tables.get(id).ok_or(EnvironmentError::LookupTableMissing)?;
            let row = table.0.get(index).ok_or(EnvironmentError::LookupValueMissing)?;
            Ok((row.0, row.1, row.2))
        })?;

        let vars = (
            Self::new_variable(Mode::Private, a),
            Self::new_variable(Mode::Private, b),
            Self::new_variable(Mode::Private, c),
        );
        Self::enforce_lookup(|| vars.clone());
        Ok(vars)
    }

    fn enforce_lookup<Fn, A, B, C>(constraint: Fn)
    where
        Fn: FnOnce() -> (A, B, C),
        A: Into<LinearCombination<Self::BaseField>>,
        B: Into<LinearCombination<Self::BaseField>>,
        C: Into<LinearCombination<Self::BaseField>>,
    {
        IN_WITNESS.with(|in_witness| {
            // Ensure we are not in witness mode.
            if !(*(**in_witness).borrow()) {
                CIRCUIT.with(|circuit| {
                    let (a, b, c) = constraint();
                    let (a, b, c) = (a.into(), b.into(), c.into());

                    // Construct the constraint object.
                    // TODO: fix right table index
                    let constraint =
                        Constraint::LookupConstraint(BaseConstraint((**circuit).borrow().scope(), a, b, c), 0);
                    // Append the constraint.
                    (**circuit).borrow_mut().enforce_lookup(constraint)
                });
            }
        })
    }
}
