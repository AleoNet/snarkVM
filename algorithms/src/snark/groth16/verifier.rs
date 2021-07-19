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

use super::{PreparedVerifyingKey, Proof, VerifyingKey};
use snarkvm_curves::traits::{PairingCurve, PairingEngine};
use snarkvm_r1cs::errors::SynthesisError;

use core::ops::{AddAssign, Mul, Neg};

pub fn prepare_verifying_key<E: PairingEngine>(vk: VerifyingKey<E>) -> PreparedVerifyingKey<E> {
    let alpha_g1_beta_g2 = E::pairing(vk.alpha_g1, vk.beta_g2);
    let gamma_g2_neg_pc = vk.gamma_g2.neg().prepare();
    let delta_g2_neg_pc = vk.delta_g2.neg().prepare();

    PreparedVerifyingKey {
        vk,
        alpha_g1_beta_g2,
        gamma_g2_neg_pc,
        delta_g2_neg_pc,
    }
}

pub fn verify_proof<E: PairingEngine>(
    pvk: &PreparedVerifyingKey<E>,
    proof: &Proof<E>,
    public_inputs: &[E::Fr],
) -> Result<bool, SynthesisError> {
    if (public_inputs.len() + 1) != pvk.gamma_abc_g1().len() {
        return Err(SynthesisError::MalformedVerifyingKey(
            public_inputs.len() + 1,
            pvk.gamma_abc_g1().len(),
        ));
    }

    let mut g_ic = pvk.gamma_abc_g1()[0];
    for (i, b) in public_inputs.iter().zip(pvk.gamma_abc_g1().iter().skip(1)) {
        g_ic.add_assign(b.mul(*i));
    }

    let qap = E::miller_loop(
        [
            (&proof.a.prepare(), &proof.b.prepare()),
            (&g_ic.prepare(), &pvk.gamma_g2_neg_pc),
            (&proof.c.prepare(), &pvk.delta_g2_neg_pc),
        ]
        .iter()
        .copied(),
    );

    let test = E::final_exponentiation(&qap).ok_or(SynthesisError::UnexpectedIdentity)?;

    Ok(test == pvk.alpha_g1_beta_g2)
}
