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

use super::{generator::KeypairAssembly, prover::ProvingAssignment, Vec};
use crate::{cfg_into_iter, cfg_iter, cfg_iter_mut, fft::EvaluationDomain};
use snarkvm_curves::traits::PairingEngine;
use snarkvm_fields::Zero;
use snarkvm_r1cs::{
    errors::{SynthesisError, SynthesisResult},
    ConstraintSystem,
    Index,
};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

#[inline]
fn get_var_index(index: Index, num_public_variables: usize) -> usize {
    match index {
        Index::Public(i) => i,
        Index::Private(i) => num_public_variables + i,
    }
}

fn evaluate_constraint<E: PairingEngine>(terms: &[(E::Fr, Index)], assignment: &[E::Fr], num_input: usize) -> E::Fr {
    cfg_iter!(terms)
        .map(|&(coeff, index)| {
            let index = get_var_index(index, num_input);
            assignment[index] * coeff
        })
        .sum()
}

pub(crate) struct R1CStoQAP;

impl R1CStoQAP {
    #[inline]
    #[allow(clippy::many_single_char_names)]
    #[allow(clippy::type_complexity)]
    pub(crate) fn instance_map_with_evaluation<E: PairingEngine>(
        assembly: &KeypairAssembly<E>,
        t: &E::Fr,
    ) -> SynthesisResult<(Vec<E::Fr>, Vec<E::Fr>, Vec<E::Fr>, E::Fr, usize, usize)> {
        let domain_size = assembly.num_constraints() + (assembly.num_public_variables - 1) + 1;
        let domain = EvaluationDomain::<E::Fr>::new(domain_size).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let domain_size = domain.size();

        let zt = domain.evaluate_vanishing_polynomial(*t);

        // Evaluate all Lagrange polynomials
        let coefficients_time = start_timer!(|| "Evaluate Lagrange coefficients");
        let u = domain.evaluate_all_lagrange_coefficients(*t);
        end_timer!(coefficients_time);

        let qap_num_variables = (assembly.num_public_variables - 1) + assembly.num_private_variables;

        let mut a = vec![E::Fr::zero(); qap_num_variables + 1];
        let mut b = vec![E::Fr::zero(); qap_num_variables + 1];
        let mut c = vec![E::Fr::zero(); qap_num_variables + 1];

        for i in 0..assembly.num_public_variables {
            a[i] = u[assembly.num_constraints() + i];
        }

        for (i, x) in u.iter().enumerate().take(assembly.num_constraints()) {
            for &(ref coeff, index) in assembly.at[i].iter() {
                let index = get_var_index(index, assembly.num_public_variables);
                a[index] += *x * coeff;
            }
            for &(ref coeff, index) in assembly.bt[i].iter() {
                let index = get_var_index(index, assembly.num_public_variables);
                b[index] += u[i] * coeff;
            }
            for &(ref coeff, index) in assembly.ct[i].iter() {
                let index = get_var_index(index, assembly.num_public_variables);
                c[index] += u[i] * coeff;
            }
        }

        Ok((a, b, c, zt, qap_num_variables, domain_size))
    }

    #[inline]
    pub(crate) fn witness_map<E: PairingEngine>(prover: &ProvingAssignment<E>) -> SynthesisResult<Vec<E::Fr>> {
        let num_inputs = prover.public_variables.len();
        let num_constraints = prover.num_constraints();

        let full_input_assignment = [&prover.public_variables[..], &prover.private_variables[..]].concat();

        let domain = EvaluationDomain::<E::Fr>::new(num_constraints + num_inputs)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let mut evaluated = cfg_into_iter!([&prover.at, &prover.bt, &prover.ct])
            .map(|cstr| evaluate_constraints::<E>(cstr, &full_input_assignment, &domain, num_constraints, num_inputs))
            .collect::<Vec<_>>();

        let mut c = evaluated.pop().unwrap();
        let mut b = evaluated.pop().unwrap();
        let mut a = evaluated.pop().unwrap();

        a[num_constraints..(num_inputs + num_constraints)].clone_from_slice(&full_input_assignment[..num_inputs]);

        cfg_into_iter!([&mut a, &mut b, &mut c]).for_each(|cstr| {
            domain.ifft_in_place(cstr);
            domain.coset_fft_in_place(cstr);
        });

        let mut ab = domain.mul_polynomials_in_evaluation_domain(&a, &b);
        drop(a);
        drop(b);

        cfg_iter_mut!(ab).zip(c).for_each(|(ab_i, c_i)| *ab_i -= &c_i);

        domain.divide_by_vanishing_poly_on_coset_in_place(&mut ab);
        domain.coset_ifft_in_place(&mut ab);

        Ok(ab)
    }
}

#[inline]
fn evaluate_constraints<E: PairingEngine>(
    constraints: &[Vec<(E::Fr, Index)>],
    full_input_assignment: &[<E as PairingEngine>::Fr],
    domain: &EvaluationDomain<E::Fr>,
    num_constraints: usize,
    num_inputs: usize,
) -> Vec<<E as PairingEngine>::Fr> {
    let mut x = vec![E::Fr::zero(); domain.size()];

    cfg_iter_mut!(x[..num_constraints])
        .zip(constraints)
        .for_each(|(x, xt_i)| {
            *x = evaluate_constraint::<E>(xt_i, full_input_assignment, num_inputs);
        });

    x
}
