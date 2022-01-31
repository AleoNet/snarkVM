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
use snarkvm_algorithms::{crh::sha256::sha256, Prepare};
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
        let mut cur = E::G1Projective::from(self.0);
        for _ in 0..128 {
            prepared_comm.push(cur.into());
            cur.double_in_place();
        }

        kzg10::PreparedCommitment::<E>(prepared_comm)
    }
}

/// `ComitterKey` is used to commit to, and create evaluation proofs for, a given
/// polynomial.
#[derive(Derivative)]
#[derivative(Default(bound = ""), Hash(bound = ""), Clone(bound = ""), Debug(bound = ""))]
#[derive(CanonicalSerialize, CanonicalDeserialize)]
pub struct CommitterKey<E: PairingEngine> {
    /// The key used to commit to polynomials.
    pub powers: Vec<E::G1Affine>,

    /// The key used to commit to hiding polynomials.
    pub powers_of_gamma_g: Vec<E::G1Affine>,

    /// The powers used to commit to shifted polynomials.
    /// This is `None` if `self` does not support enforcing any degree bounds.
    pub shifted_powers: Option<Vec<E::G1Affine>>,

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

impl<E: PairingEngine> FromBytes for CommitterKey<E> {
    fn read_le<R: Read>(mut reader: R) -> io::Result<Self> {
        // Deserialize `powers`.
        let powers_len: u32 = FromBytes::read_le(&mut reader)?;
        let mut powers = Vec::with_capacity(powers_len as usize);
        for _ in 0..powers_len {
            let power: E::G1Affine = FromBytes::read_le(&mut reader)?;
            powers.push(power);
        }

        // Deserialize `powers_of_gamma_g`.
        let powers_of_gamma_g_len: u32 = FromBytes::read_le(&mut reader)?;
        let mut powers_of_gamma_g = Vec::with_capacity(powers_of_gamma_g_len as usize);
        for _ in 0..powers_of_gamma_g_len {
            let powers_of_g: E::G1Affine = FromBytes::read_le(&mut reader)?;
            powers_of_gamma_g.push(powers_of_g);
        }

        // Deserialize `shifted_powers`.
        let has_shifted_powers: bool = FromBytes::read_le(&mut reader)?;
        let shifted_powers = match has_shifted_powers {
            true => {
                let shifted_powers_len: u32 = FromBytes::read_le(&mut reader)?;
                let mut shifted_powers = Vec::with_capacity(shifted_powers_len as usize);
                for _ in 0..shifted_powers_len {
                    let shifted_power: E::G1Affine = FromBytes::read_le(&mut reader)?;
                    shifted_powers.push(shifted_power);
                }

                Some(shifted_powers)
            }
            false => None,
        };

        // Deserialize `shifted_powers_of_gamma_g`.
        let has_shifted_powers_of_gamma_g: bool = FromBytes::read_le(&mut reader)?;
        let shifted_powers_of_gamma_g = match has_shifted_powers_of_gamma_g {
            true => {
                let mut shifted_powers_of_gamma_g = BTreeMap::new();
                let shifted_powers_of_gamma_g_num_elements: u32 = FromBytes::read_le(&mut reader)?;
                for _ in 0..shifted_powers_of_gamma_g_num_elements {
                    let key: u32 = FromBytes::read_le(&mut reader)?;

                    let value_len: u32 = FromBytes::read_le(&mut reader)?;
                    let mut value = Vec::with_capacity(value_len as usize);
                    for _ in 0..value_len {
                        let val: E::G1Affine = FromBytes::read_le(&mut reader)?;
                        value.push(val);
                    }

                    shifted_powers_of_gamma_g.insert(key as usize, value);
                }

                Some(shifted_powers_of_gamma_g)
            }
            false => None,
        };

        // Deserialize `enforced_degree_bounds`.
        let has_enforced_degree_bounds: bool = FromBytes::read_le(&mut reader)?;
        let enforced_degree_bounds = match has_enforced_degree_bounds {
            true => {
                let enforced_degree_bounds_len: u32 = FromBytes::read_le(&mut reader)?;
                let mut enforced_degree_bounds = Vec::with_capacity(enforced_degree_bounds_len as usize);
                for _ in 0..enforced_degree_bounds_len {
                    let enforced_degree_bound: u32 = FromBytes::read_le(&mut reader)?;
                    enforced_degree_bounds.push(enforced_degree_bound as usize);
                }

                Some(enforced_degree_bounds)
            }
            false => None,
        };

        // Deserialize `max_degree`.
        let max_degree: u32 = FromBytes::read_le(&mut reader)?;

        // Construct the hash of the group elements.
        let mut hash_input = powers.to_bytes_le().map_err(|_| error("Could not serialize powers"))?;

        hash_input.extend_from_slice(
            &powers_of_gamma_g.to_bytes_le().map_err(|_| error("Could not serialize powers_of_gamma_g"))?,
        );

        if let Some(shifted_powers) = &shifted_powers {
            hash_input.extend_from_slice(
                &shifted_powers.to_bytes_le().map_err(|_| error("Could not serialize shifted_powers"))?,
            );
        }

        if let Some(shifted_powers_of_gamma_g) = &shifted_powers_of_gamma_g {
            for value in shifted_powers_of_gamma_g.values() {
                hash_input.extend_from_slice(
                    &value.to_bytes_le().map_err(|_| error("Could not serialize shifted_power_of_gamma_g"))?,
                );
            }
        }

        // Deserialize `hash`.
        let hash = sha256(&hash_input);
        let expected_hash: [u8; 32] = FromBytes::read_le(&mut reader)?;

        // Enforce the group elements construct the expected hash.
        if expected_hash != hash {
            return Err(error("Mismatching group elements"));
        }

        Ok(Self {
            powers,
            powers_of_gamma_g,
            shifted_powers,
            shifted_powers_of_gamma_g,
            enforced_degree_bounds,
            max_degree: max_degree as usize,
        })
    }
}

impl<E: PairingEngine> ToBytes for CommitterKey<E> {
    fn write_le<W: Write>(&self, mut writer: W) -> io::Result<()> {
        // Serialize `powers`.
        (self.powers.len() as u32).write_le(&mut writer)?;
        for power in &self.powers {
            power.write_le(&mut writer)?;
        }

        // Serialize `powers_of_gamma_g`.
        (self.powers_of_gamma_g.len() as u32).write_le(&mut writer)?;
        for power_of_gamma_g in &self.powers_of_gamma_g {
            power_of_gamma_g.write_le(&mut writer)?;
        }

        // Serialize `shifted_powers`.
        self.shifted_powers.is_some().write_le(&mut writer)?;
        if let Some(shifted_powers) = &self.shifted_powers {
            (shifted_powers.len() as u32).write_le(&mut writer)?;
            for shifted_power in shifted_powers {
                shifted_power.write_le(&mut writer)?;
            }
        }

        // Serialize `shifted_powers_of_gamma_g`.
        self.shifted_powers_of_gamma_g.is_some().write_le(&mut writer)?;
        if let Some(shifted_powers_of_gamma_g) = &self.shifted_powers_of_gamma_g {
            (shifted_powers_of_gamma_g.len() as u32).write_le(&mut writer)?;
            for (key, shifted_powers) in shifted_powers_of_gamma_g {
                (*key as u32).write_le(&mut writer)?;
                (shifted_powers.len() as u32).write_le(&mut writer)?;
                for shifted_power in shifted_powers {
                    shifted_power.write_le(&mut writer)?;
                }
            }
        }

        // Serialize `enforced_degree_bounds`.
        self.enforced_degree_bounds.is_some().write_le(&mut writer)?;
        if let Some(enforced_degree_bounds) = &self.enforced_degree_bounds {
            (enforced_degree_bounds.len() as u32).write_le(&mut writer)?;
            for enforced_degree_bound in enforced_degree_bounds {
                (*enforced_degree_bound as u32).write_le(&mut writer)?;
            }
        }

        // Serialize `max_degree`.
        (self.max_degree as u32).write_le(&mut writer)?;

        // Construct the hash of the group elements.
        let mut hash_input = self.powers.to_bytes_le().map_err(|_| error("Could not serialize powers"))?;

        hash_input.extend_from_slice(
            &self.powers_of_gamma_g.to_bytes_le().map_err(|_| error("Could not serialize powers_of_gamma_g"))?,
        );

        if let Some(shifted_powers) = &self.shifted_powers {
            hash_input.extend_from_slice(
                &shifted_powers.to_bytes_le().map_err(|_| error("Could not serialize shifted_powers"))?,
            );
        }

        if let Some(shifted_powers_of_gamma_g) = &self.shifted_powers_of_gamma_g {
            for value in shifted_powers_of_gamma_g.values() {
                hash_input.extend_from_slice(
                    &value.to_bytes_le().map_err(|_| error("Could not serialize shifted_power_of_gamma_g"))?,
                );
            }
        }

        // Serialize `hash`
        let hash = sha256(&hash_input);
        hash.write_le(&mut writer)
    }
}

impl<E: PairingEngine> CommitterKey<E> {
    /// Obtain powers for the underlying KZG10 construction
    pub fn powers(&self) -> kzg10::Powers<E> {
        kzg10::Powers {
            powers_of_g: self.powers.as_slice().into(),
            powers_of_gamma_g: self.powers_of_gamma_g.as_slice().into(),
        }
    }

    /// Obtain powers for committing to shifted polynomials.
    pub fn shifted_powers(&self, degree_bound: impl Into<Option<usize>>) -> Option<kzg10::Powers<E>> {
        match (&self.shifted_powers, &self.shifted_powers_of_gamma_g) {
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
        self.powers.len() - 1
    }
}

/// `VerifierKey` is used to check evaluation proofs for a given commitment.
#[derive(Derivative, CanonicalSerialize, CanonicalDeserialize)]
#[derivative(Default(bound = ""), Clone(bound = ""), Debug(bound = ""), PartialEq(bound = ""), Eq(bound = ""))]
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
        self.degree_bounds_and_neg_powers_of_h
            .as_ref()
            .and_then(|v| v.binary_search_by(|(d, _)| d.cmp(&degree_bound)).ok().map(|i| v[i].1))
    }

    pub fn get_prepared_shift_power(&self, degree_bound: usize) -> Option<<E::G2Affine as PairingCurve>::Prepared> {
        self.degree_bounds_and_prepared_neg_powers_of_h
            .as_ref()
            .and_then(|v| v.binary_search_by(|(d, _)| d.cmp(&degree_bound)).ok().map(|i| v[i].1.clone()))
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
            for (d, neg_powers_of_h) in degree_bounds_and_neg_powers_of_h.iter() {
                let d_elem: E::Fq = (*d as u64).into();
                res.push(d_elem);
                res.append(&mut neg_powers_of_h.to_field_elements()?);
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
