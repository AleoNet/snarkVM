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

use crate::r1cs::{ConstraintSynthesizer, ConstraintSystem, LookupTable, SynthesisError}; // TODO: consider renaming R1CS or moving lookuptable to a lookup crate?
use snarkvm_fields::Field;

use rand::{CryptoRng, Rng};

#[doc(hidden)]
#[derive(Clone)]
/// This Circuit is only for testing and should not be used in production
pub struct TestCircuit<F: Field> {
    pub a: Option<F>,
    pub b: Option<F>,
    pub num_constraints: usize,
    pub num_lookups: usize,
    pub num_variables: usize,
    pub mul_depth: usize,
    pub tables: Option<Vec<LookupTable<F>>>,
}

impl<F: Field> core::fmt::Debug for TestCircuit<F> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "TestCircuit {{ num_constraints: {}, num_variables: {}, mul_depth: {} }}",
            self.num_constraints, self.num_variables, self.mul_depth
        )
    }
}

impl<ConstraintF: Field> ConstraintSynthesizer<ConstraintF> for TestCircuit<ConstraintF> {
    fn generate_constraints<CS: ConstraintSystem<ConstraintF>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
        // TODO: add tests that by the end we really end up with these numbers of constraints and variables
        assert!(self.num_constraints > self.mul_depth + self.num_lookups);
        assert!(self.num_variables > 2 + self.mul_depth);

        let mut lookup_vars = Vec::with_capacity(self.num_lookups);
        let mut entries_per_table = 0;
        let mut lookups_per_table_entry = 0;
        let mut num_tables = 0;
        if let Some(tables) = self.tables.as_ref() {
            num_tables = tables.len();
            let num_table_entries = tables.iter().map(|t| t.table.len()).sum::<usize>();
            assert!(!tables.is_empty());
            assert!(num_table_entries > 0);
            entries_per_table = num_table_entries / tables.len();
            lookups_per_table_entry = (self.num_lookups / num_table_entries).max(1);
            for (i, table) in tables.iter().enumerate() {
                for (j, (key, &val)) in table.table.iter().enumerate() {
                    // Only declare new lookup variables when all the following conditions hold:
                    // (1) we declared less lookup variables than the number of lookups we want to perform
                    // (2) we declared less lookup variables than the number of table entries
                    if lookup_vars.len() < self.num_lookups && lookup_vars.len() < num_table_entries {
                        let key_0 = cs.alloc(|| format!("key_0_{i}_{j}"), || Ok(key[0]))?;
                        let key_1 = cs.alloc(|| format!("key_1_{i}_{j}"), || Ok(key[1]))?;
                        let val = cs.alloc(|| format!("val_{i}_{j}"), || Ok(val))?;
                        lookup_vars.push([key_0, key_1, val]);
                    }
                }
                cs.add_lookup_table(table.clone());
            }
        }
        let mul_depth_constraints = self.mul_depth - 1;
        let mul_constraints = self.num_constraints - mul_depth_constraints - self.num_lookups;
        let num_dummy_variables = self.num_variables - 2 - self.mul_depth; // extra variables not used in any constraints.

        let a = cs.alloc(|| "a", || self.a.ok_or(SynthesisError::AssignmentMissing))?;
        let b = cs.alloc(|| "b", || self.b.ok_or(SynthesisError::AssignmentMissing))?;

        let mut mul_vars = Vec::with_capacity(self.mul_depth);
        for i in 0..self.mul_depth {
            let mul_var = cs.alloc_input(
                || format!("mul_var {i}"),
                || {
                    let mut a = self.a.ok_or(SynthesisError::AssignmentMissing)?;
                    let b = self.b.ok_or(SynthesisError::AssignmentMissing)?;

                    for _ in 0..(1 + i) {
                        a.mul_assign(&b);
                    }
                    Ok(a)
                },
            )?;
            mul_vars.push(mul_var);
        }

        for i in 0..num_dummy_variables {
            let _ = cs.alloc(|| format!("var {i}"), || self.a.ok_or(SynthesisError::AssignmentMissing))?;
        }

        for i in 0..mul_constraints {
            cs.enforce(|| format!("constraint {i}"), |lc| lc + a, |lc| lc + b, |lc| lc + mul_vars[0]);
        }

        // We make sure to test a varying amount of lookups, tables and table entries
        let mut lookups_constrained = 0;
        let mut lookup_var_index = 0;
        'outer: for (table_index, t) in (0..num_tables).enumerate() {
            for i in 0..entries_per_table {
                for j in 0..lookups_per_table_entry {
                    cs.enforce_lookup(
                        || format!("lookup {t}_{i}_{j}"),
                        |lc| lc + lookup_vars[lookup_var_index][0],
                        |lc| lc + lookup_vars[lookup_var_index][1],
                        |lc| lc + lookup_vars[lookup_var_index][2],
                        table_index,
                    )?;
                    lookups_constrained += 1;
                    if lookups_constrained == self.num_lookups {
                        break 'outer;
                    }
                }
                if lookup_var_index < lookup_vars.len() - 1 {
                    lookup_var_index += 1;
                }
            }
        }

        for i in 0..mul_depth_constraints {
            cs.enforce(|| format!("constraint_mul {i}"), |lc| lc + mul_vars[i], |lc| lc + b, |lc| lc + mul_vars[i + 1]);
        }

        Ok(())
    }
}

impl<F: Field> TestCircuit<F> {
    pub fn gen_rand<R: Rng + CryptoRng>(
        mul_depth: usize,
        num_constraints: usize,
        num_variables: usize,
        num_lookups: usize,
        tables: Option<Vec<LookupTable<F>>>,
        rng: &mut R,
    ) -> (Self, Vec<F>) {
        let mut public_inputs: Vec<F> = Vec::with_capacity(mul_depth);
        let a = F::rand(rng);
        let b = F::rand(rng);

        for j in 1..(mul_depth + 1) {
            let mut new_var = a;
            for _ in 0..j {
                new_var.mul_assign(&b);
            }
            public_inputs.push(new_var);
        }

        (
            TestCircuit { a: Some(a), b: Some(b), num_constraints, num_variables, mul_depth, num_lookups, tables },
            public_inputs,
        )
    }

    pub fn gen_lookup_table<R: Rng + CryptoRng>(
        num_entries: usize,
        num_tables: usize,
        rng: &mut R,
    ) -> Option<Vec<LookupTable<F>>> {
        if num_tables == 0 {
            return None;
        }

        let a = F::rand(rng);
        let b = F::rand(rng);

        let num_entries_per_table = num_entries / num_tables;
        let mut tables = Vec::with_capacity(num_tables);
        let mut table_entry_index = 0u64;
        for _ in 0..num_tables {
            let mut table = LookupTable::default();
            for _ in 0..num_entries_per_table {
                let lookup_value = [a.pow([table_entry_index]), a];
                table.fill(lookup_value, b);
                table_entry_index += 1;
            }
            tables.push(table);
        }
        assert_eq!(table_entry_index, num_entries as u64);

        Some(tables)
    }
}
