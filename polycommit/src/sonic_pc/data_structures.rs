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

use crate::{impl_bytes, kzg10, BTreeMap, PCCommitterKey, PCVerifierKey, Vec};
use snarkvm_algorithms::Prepare;
use snarkvm_curves::{
    traits::{PairingCurve, PairingEngine},
    Group,
};
use snarkvm_fields::{ConstraintFieldError, ToConstraintField};
use snarkvm_utilities::{error, errors::SerializationError, serialize::*, FromBytes, ToBytes};

/// `UniversalParams` are the universal parameters for the KZG10 scheme.
pub type UniversalParams<E> = kzg10::UniversalParams<E>;

/// `Randomness` is the randomness for the KZG10 scheme.
pub type Randomness<E> = kzg10::Randomness<E>;

/// `Commitment` is the commitment for the KZG10 scheme.
pub type Commitment<E> = kzg10::Commitment<E>;

/// `PreparedCommitment` is the prepared commitment for the KZG10 scheme.
pub type PreparedCommitment<E> = kzg10::PreparedCommitment<E>;

impl<E: PairingEngine> Prepare<PreparedCommitment<E>> for Commitment<E> {
    /// prepare `PreparedCommitment` from `Commitment`
    fn prepare(&self) -> PreparedCommitment<E> {
        let mut prepared_comm = Vec::<E::G1Affine>::new();
        let mut cur = E::G1Projective::from(self.0.clone());
        for _ in 0..128 {
            prepared_comm.push(cur.clone().into());
            cur.double_in_place();
        }

        PreparedCommitment::<E> { 0: prepared_comm }
    }
}

/// `ComitterKey` is used to commit to, and create evaluation proofs for, a given
/// polynomial.
#[derive(Derivative)]
#[derivative(Default(bound = ""), Hash(bound = ""), Clone(bound = ""), Debug(bound = ""))]
#[derive(CanonicalSerialize, CanonicalDeserialize)]
pub struct CommitterKey<E: PairingEngine> {
    /// The key used to commit to polynomials.
    pub powers_of_g: Vec<E::G1Affine>,

    /// The key used to commit to hiding polynomials.
    pub powers_of_gamma_g: Vec<E::G1Affine>,

    /// The powers used to commit to shifted polynomials.
    /// This is `None` if `self` does not support enforcing any degree bounds.
    pub shifted_powers_of_g: Option<Vec<E::G1Affine>>,

    /// The powers used to commit to shifted hiding polynomials.
    /// This is `None` if `self` does not support enforcing any degree bounds.
    pub shifted_powers_of_gamma_g: Option<BTreeMap<usize, Vec<E::G1Affine>>>,

    /// The degree bounds that are supported by `self`.
    /// Sorted in ascending order from smallest bound to largest bound.
    /// This is `None` if `self` does not support enforcing any degree bounds.
    pub enforced_degree_bounds: Option<Vec<usize>>,

    /// The maximum degree supported by the `UniversalParams` from which `self` was derived
    pub max_degree: usize,
}
impl_bytes!(CommitterKey);

impl<E: PairingEngine> CommitterKey<E> {
    /// Obtain powers for the underlying KZG10 construction
    pub fn powers(&self) -> kzg10::Powers<E> {
        kzg10::Powers {
            powers_of_g: self.powers_of_g.as_slice().into(),
            powers_of_gamma_g: self.powers_of_gamma_g.as_slice().into(),
        }
    }

    /// Obtain powers for committing to shifted polynomials.
    pub fn shifted_powers(&self, degree_bound: impl Into<Option<usize>>) -> Option<kzg10::Powers<E>> {
        match (&self.shifted_powers_of_g, &self.shifted_powers_of_gamma_g) {
            (Some(shifted_powers_of_g), Some(shifted_powers_of_gamma_g)) => {
                let max_bound = self.enforced_degree_bounds.as_ref().unwrap().last().unwrap();
                let (bound, powers_range) = if let Some(degree_bound) = degree_bound.into() {
                    assert!(self.enforced_degree_bounds.as_ref().unwrap().contains(&degree_bound));
                    (degree_bound, (max_bound - degree_bound)..)
                } else {
                    (*max_bound, 0..)
                };

                let ck = kzg10::Powers {
                    powers_of_g: shifted_powers_of_g[powers_range].into(),
                    powers_of_gamma_g: shifted_powers_of_gamma_g[&bound].clone().into(),
                };

                Some(ck)
            }

            (_, _) => None,
        }
    }
}

impl<E: PairingEngine> PCCommitterKey for CommitterKey<E> {
    fn max_degree(&self) -> usize {
        self.max_degree
    }

    fn supported_degree(&self) -> usize {
        self.powers_of_g.len() - 1
    }
}

/// `VerifierKey` is used to check evaluation proofs for a given commitment.
#[derive(Derivative)]
#[derivative(Default(bound = ""), Clone(bound = ""), Debug(bound = ""))]
#[derive(CanonicalSerialize, CanonicalDeserialize)]
pub struct VerifierKey<E: PairingEngine> {
    /// The verification key for the underlying KZG10 scheme.
    pub vk: kzg10::VerifierKey<E>,

    /// Pairs a degree_bound with its corresponding G2 element.
    /// Each pair is in the form `(degree_bound, \beta^{degree_bound - max_degree} h),` where `h` is the generator of G2 above
    pub degree_bounds_and_neg_powers_of_h: Option<Vec<(usize, E::G2Affine)>>,

    /// The prepared version of `degree_bounds_and_neg_powers_of_h`.
    pub degree_bounds_and_prepared_neg_powers_of_h: Option<Vec<(usize, <E::G2Affine as PairingCurve>::Prepared)>>,

    /// The maximum degree supported by the trimmed parameters that `self` is
    /// a part of.
    pub supported_degree: usize,

    /// The maximum degree supported by the `UniversalParams` `self` was derived
    /// from.
    pub max_degree: usize,
}
impl_bytes!(VerifierKey);

impl<E: PairingEngine> VerifierKey<E> {
    /// Find the appropriate shift for the degree bound.
    pub fn get_shift_power(&self, degree_bound: usize) -> Option<E::G2Affine> {
        self.degree_bounds_and_neg_powers_of_h.as_ref().and_then(|v| {
            v.binary_search_by(|(d, _)| d.cmp(&degree_bound))
                .ok()
                .map(|i| v[i].1.clone())
        })
    }

    pub fn get_prepared_shift_power(&self, degree_bound: usize) -> Option<<E::G2Affine as PairingCurve>::Prepared> {
        self.degree_bounds_and_prepared_neg_powers_of_h.as_ref().and_then(|v| {
            v.binary_search_by(|(d, _)| d.cmp(&degree_bound))
                .ok()
                .map(|i| v[i].1.clone())
        })
    }
}

impl<E: PairingEngine> PCVerifierKey for VerifierKey<E> {
    fn max_degree(&self) -> usize {
        self.max_degree
    }

    fn supported_degree(&self) -> usize {
        self.supported_degree
    }
}

impl<E: PairingEngine> ToConstraintField<E::Fq> for VerifierKey<E> {
    fn to_field_elements(&self) -> Result<Vec<E::Fq>, ConstraintFieldError> {
        let mut res = Vec::new();
        res.extend_from_slice(&self.vk.to_field_elements()?);

        if let Some(degree_bounds_and_neg_powers_of_h) = &self.degree_bounds_and_neg_powers_of_h {
            for (d, _neg_powers_of_h) in degree_bounds_and_neg_powers_of_h.iter() {
                let d_elem: E::Fq = (*d as u64).into();

                res.push(d_elem);
            }
        }

        Ok(res)
    }
}

/// `PreparedVerifierKey` is used to check evaluation proofs for a given commitment.
#[derive(Derivative)]
#[derivative(Clone(bound = ""), Debug(bound = ""))]
pub struct PreparedVerifierKey<E: PairingEngine> {
    /// The verification key for the underlying KZG10 scheme.
    pub prepared_vk: kzg10::PreparedVerifierKey<E>,
    /// Information required to enforce degree bounds. Each pair
    /// is of the form `(degree_bound, shifting_advice)`.
    /// This is `None` if `self` does not support enforcing any degree bounds.
    pub degree_bounds_and_prepared_neg_powers_of_h: Option<Vec<(usize, <E::G2Affine as PairingCurve>::Prepared)>>,
    /// The maximum degree supported by the `UniversalParams` `self` was derived
    /// from.
    pub max_degree: usize,
    /// The maximum degree supported by the trimmed parameters that `self` is
    /// a part of.
    pub supported_degree: usize,
}

impl<E: PairingEngine> PreparedVerifierKey<E> {
    /// Find the appropriate shift for the degree bound.
    pub fn get_prepared_shift_power(&self, bound: usize) -> Option<<E::G2Affine as PairingCurve>::Prepared> {
        self.degree_bounds_and_prepared_neg_powers_of_h
            .as_ref()
            .and_then(|v| v.binary_search_by(|(d, _)| d.cmp(&bound)).ok().map(|i| v[i].1.clone()))
    }
}

impl<E: PairingEngine> Prepare<PreparedVerifierKey<E>> for VerifierKey<E> {
    /// prepare `PreparedVerifierKey` from `VerifierKey`
    fn prepare(&self) -> PreparedVerifierKey<E> {
        let prepared_vk = kzg10::PreparedVerifierKey::<E>::prepare(&self.vk);

        PreparedVerifierKey::<E> {
            prepared_vk,
            degree_bounds_and_prepared_neg_powers_of_h: self.degree_bounds_and_prepared_neg_powers_of_h.clone(),
            max_degree: self.max_degree,
            supported_degree: self.supported_degree,
        }
    }
}

/// Evaluation proof at a query set.
#[derive(Derivative)]
#[derivative(
    Default(bound = ""),
    Hash(bound = ""),
    Clone(bound = ""),
    Debug(bound = ""),
    PartialEq(bound = ""),
    Eq(bound = "")
)]
pub struct BatchProof<E: PairingEngine>(pub(crate) Vec<kzg10::Proof<E>>);
