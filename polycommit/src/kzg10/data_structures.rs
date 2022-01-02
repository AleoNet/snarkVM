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

use crate::{impl_bytes, BTreeMap, *};
use core::ops::{Add, AddAssign};
use snarkvm_curves::{
    traits::{AffineCurve, PairingCurve, PairingEngine, ProjectiveCurve},
    Group,
};
use snarkvm_fields::{ConstraintFieldError, PrimeField, ToConstraintField, Zero};
use snarkvm_utilities::{
    error,
    errors::SerializationError,
    serialize::{CanonicalDeserialize, CanonicalSerialize},
    FromBytes,
    ToBytes,
};

use core::ops::Mul;

/// `UniversalParams` are the universal parameters for the KZG10 scheme.
#[derive(Derivative)]
#[derivative(Default(bound = ""), Clone(bound = ""), Debug(bound = ""))]
#[derive(CanonicalSerialize, CanonicalDeserialize)]
pub struct UniversalParams<E: PairingEngine> {
    /// Group elements of the form `{ \beta^i G }`, where `i` ranges from 0 to `degree`.
    pub powers_of_g: Vec<E::G1Affine>,
    /// Group elements of the form `{ \beta^i \gamma G }`, where `i` ranges from 0 to `degree`.
    pub powers_of_gamma_g: BTreeMap<usize, E::G1Affine>,
    /// The generator of G2.
    pub h: E::G2Affine,
    /// \beta times the above generator of G2.
    pub beta_h: E::G2Affine,
    /// Supported degree bounds.
    pub supported_degree_bounds: Vec<usize>,
    /// Group elements of the form `{ \beta^{max_degree - i} G1}`, where `i` is the supported degree bound.
    /// This one is used for deriving the verifying key.
    pub inverse_powers_of_g: BTreeMap<usize, E::G1Affine>,
    /// Group elements of the form `{ \beta^{max_degree -i} G2 }`, where `i` is the supported degree bound.
    /// This one is used for deriving the verifying key.
    pub inverse_neg_powers_of_h: BTreeMap<usize, E::G2Affine>,
    /// The generator of G2, prepared for use in pairings.
    #[derivative(Debug = "ignore")]
    pub prepared_h: <E::G2Affine as PairingCurve>::Prepared,
    /// \beta times the above generator of G2, prepared for use in pairings.
    #[derivative(Debug = "ignore")]
    pub prepared_beta_h: <E::G2Affine as PairingCurve>::Prepared,
}

impl<E: PairingEngine> FromBytes for UniversalParams<E> {
    fn read_le<R: Read>(mut reader: R) -> io::Result<Self> {
        // Deserialize `powers_of_g`.
        let powers_of_g_len: u32 = FromBytes::read_le(&mut reader)?;
        let mut powers_of_g = Vec::with_capacity(powers_of_g_len as usize);
        for _ in 0..powers_of_g_len {
            let power_of_g: E::G1Affine = FromBytes::read_le(&mut reader)?;
            powers_of_g.push(power_of_g);
        }

        // Deserialize `powers_of_gamma_g`.
        let mut powers_of_gamma_g = BTreeMap::new();
        let powers_of_gamma_g_num_elements: u32 = FromBytes::read_le(&mut reader)?;
        for _ in 0..powers_of_gamma_g_num_elements {
            let key: u32 = FromBytes::read_le(&mut reader)?;
            let power_of_gamma_g: E::G1Affine = FromBytes::read_le(&mut reader)?;

            powers_of_gamma_g.insert(key as usize, power_of_gamma_g);
        }

        // Deserialize `h`.
        let h: E::G2Affine = FromBytes::read_le(&mut reader)?;

        // Deserialize `beta_h`.
        let beta_h: E::G2Affine = FromBytes::read_le(&mut reader)?;

        // Deserialize `supported_degree_bounds`.
        let supported_degree_bounds_len: u32 = FromBytes::read_le(&mut reader)?;
        let mut supported_degree_bounds = Vec::with_capacity(supported_degree_bounds_len as usize);
        for _ in 0..supported_degree_bounds_len {
            let degree_bound: u32 = FromBytes::read_le(&mut reader)?;
            supported_degree_bounds.push(degree_bound as usize);
        }

        // Deserialize `inverse_powers_of_g`.
        let mut inverse_powers_of_g = BTreeMap::new();
        let inverse_powers_of_g_num_elements: u32 = FromBytes::read_le(&mut reader)?;
        for _ in 0..inverse_powers_of_g_num_elements {
            let key: u32 = FromBytes::read_le(&mut reader)?;
            let inverse_power_of_g: E::G1Affine = FromBytes::read_le(&mut reader)?;

            inverse_powers_of_g.insert(key as usize, inverse_power_of_g);
        }

        // Deserialize `inverse_neg_powers_of_h`.
        let mut inverse_neg_powers_of_h = BTreeMap::new();
        let inverse_neg_powers_of_h_num_elements: u32 = FromBytes::read_le(&mut reader)?;
        for _ in 0..inverse_neg_powers_of_h_num_elements {
            let key: u32 = FromBytes::read_le(&mut reader)?;
            let neg_power_of_h: E::G2Affine = FromBytes::read_le(&mut reader)?;

            inverse_neg_powers_of_h.insert(key as usize, neg_power_of_h);
        }

        // Deserialize `prepared_h`.
        let prepared_h: <E::G2Affine as PairingCurve>::Prepared = FromBytes::read_le(&mut reader)?;

        // Deserialize `prepared_beta_h`.
        let prepared_beta_h: <E::G2Affine as PairingCurve>::Prepared = FromBytes::read_le(&mut reader)?;

        Ok(Self {
            powers_of_g,
            powers_of_gamma_g,
            h,
            beta_h,
            supported_degree_bounds,
            inverse_powers_of_g,
            inverse_neg_powers_of_h,
            prepared_h,
            prepared_beta_h,
        })
    }
}

impl<E: PairingEngine> ToBytes for UniversalParams<E> {
    fn write_le<W: Write>(&self, mut writer: W) -> io::Result<()> {
        // Serialize `powers_of_g`.
        (self.powers_of_g.len() as u32).write_le(&mut writer)?;
        for power in &self.powers_of_g {
            power.write_le(&mut writer)?;
        }

        // Serialize `powers_of_gamma_g`.
        (self.powers_of_gamma_g.len() as u32).write_le(&mut writer)?;
        for (key, power_of_gamma_g) in &self.powers_of_gamma_g {
            (*key as u32).write_le(&mut writer)?;
            power_of_gamma_g.write_le(&mut writer)?;
        }

        // Serialize `h`.
        self.h.write_le(&mut writer)?;

        // Serialize `beta_h`.
        self.beta_h.write_le(&mut writer)?;

        // Serialize `supported_degree_bounds`.
        (self.supported_degree_bounds.len() as u32).write_le(&mut writer)?;
        for degree_bound in &self.supported_degree_bounds {
            (*degree_bound as u32).write_le(&mut writer)?;
        }

        // Serialize `inverse_powers_of_g`.
        (self.inverse_powers_of_g.len() as u32).write_le(&mut writer)?;
        for (key, inverse_power_of_g) in &self.inverse_powers_of_g {
            (*key as u32).write_le(&mut writer)?;
            inverse_power_of_g.write_le(&mut writer)?;
        }

        // Serialize `inverse_neg_powers_of_h`.
        (self.inverse_neg_powers_of_h.len() as u32).write_le(&mut writer)?;
        for (key, inverse_neg_power_of_g) in &self.inverse_neg_powers_of_h {
            (*key as u32).write_le(&mut writer)?;
            inverse_neg_power_of_g.write_le(&mut writer)?;
        }

        // Serialize `prepared_h`.
        self.prepared_h.write_le(&mut writer)?;

        // Serialize `prepared_beta_h`.
        self.prepared_beta_h.write_le(&mut writer)?;

        Ok(())
    }
}

impl<E: PairingEngine> PCUniversalParams for UniversalParams<E> {
    fn max_degree(&self) -> usize {
        self.powers_of_g.len() - 1
    }

    fn supported_degree_bounds(&self) -> &[usize] {
        &self.supported_degree_bounds
    }
}

/// `Powers` is used to commit to and create evaluation proofs for a given
/// polynomial.
#[derive(Derivative)]
#[derivative(Default(bound = ""), Hash(bound = ""), Clone(bound = ""), Debug(bound = ""))]
pub struct Powers<'a, E: PairingEngine> {
    /// Group elements of the form `β^i G`, for different values of `i`.
    pub powers_of_g: Cow<'a, [E::G1Affine]>,
    /// Group elements of the form `β^i γG`, for different values of `i`.
    pub powers_of_gamma_g: Cow<'a, [E::G1Affine]>,
}

impl<E: PairingEngine> Powers<'_, E> {
    /// The number of powers in `self`.
    pub fn size(&self) -> usize {
        self.powers_of_g.len()
    }
}

/// `VerifierKey` is used to check evaluation proofs for a given commitment.
#[derive(Derivative)]
#[derivative(Default(bound = ""), Clone(bound = ""), Debug(bound = ""))]
#[derive(CanonicalSerialize, CanonicalDeserialize)]
pub struct VerifierKey<E: PairingEngine> {
    /// The generator of G1.
    pub g: E::G1Affine,
    /// The generator of G1 that is used for making a commitment hiding.
    pub gamma_g: E::G1Affine,
    /// The generator of G2.
    pub h: E::G2Affine,
    /// \beta times the above generator of G2.
    pub beta_h: E::G2Affine,
    /// The generator of G2, prepared for use in pairings.
    #[derivative(Debug = "ignore")]
    pub prepared_h: <E::G2Affine as PairingCurve>::Prepared,
    /// \beta times the above generator of G2, prepared for use in pairings.
    #[derivative(Debug = "ignore")]
    pub prepared_beta_h: <E::G2Affine as PairingCurve>::Prepared,
}
impl_bytes!(VerifierKey);

impl<E: PairingEngine> ToConstraintField<E::Fq> for VerifierKey<E> {
    fn to_field_elements(&self) -> Result<Vec<E::Fq>, ConstraintFieldError> {
        let mut res = Vec::new();

        res.extend_from_slice(&self.g.to_field_elements().unwrap());
        res.extend_from_slice(&self.gamma_g.to_field_elements().unwrap());
        res.extend_from_slice(&self.h.to_field_elements().unwrap());
        res.extend_from_slice(&self.beta_h.to_field_elements().unwrap());

        Ok(res)
    }
}

/// `PreparedVerifierKey` is the fully prepared version for checking evaluation proofs for a given commitment.
/// We omit gamma here for simplicity.
#[derive(Derivative)]
#[derivative(Default(bound = ""), Clone(bound = ""), Debug(bound = ""))]
pub struct PreparedVerifierKey<E: PairingEngine> {
    /// The generator of G1, prepared for power series.
    pub prepared_g: Vec<E::G1Affine>,
    /// The generator of G1 that is used for making a commitment hiding, prepared for power series
    pub prepared_gamma_g: Vec<E::G1Affine>,
    /// The generator of G2, prepared for use in pairings.
    pub prepared_h: <E::G2Affine as PairingCurve>::Prepared,
    /// \beta times the above generator of G2, prepared for use in pairings.
    pub prepared_beta_h: <E::G2Affine as PairingCurve>::Prepared,
}

impl<E: PairingEngine> PreparedVerifierKey<E> {
    /// prepare `PreparedVerifierKey` from `VerifierKey`
    pub fn prepare(vk: &VerifierKey<E>) -> Self {
        let supported_bits = E::Fr::size_in_bits();

        let mut prepared_g = Vec::<E::G1Affine>::new();
        let mut g = E::G1Projective::from(vk.g);
        for _ in 0..supported_bits {
            prepared_g.push(g.into());
            g.double_in_place();
        }

        let mut prepared_gamma_g = Vec::<E::G1Affine>::new();
        let mut gamma_g = E::G1Projective::from(vk.gamma_g);
        for _ in 0..supported_bits {
            prepared_gamma_g.push(gamma_g.into());
            gamma_g.double_in_place();
        }

        Self {
            prepared_g,
            prepared_gamma_g,
            prepared_h: vk.prepared_h.clone(),
            prepared_beta_h: vk.prepared_beta_h.clone(),
        }
    }
}

/// `Commitment` commits to a polynomial. It is output by `KZG10::commit`.
#[derive(Derivative)]
#[derivative(
    Default(bound = ""),
    Hash(bound = ""),
    Clone(bound = ""),
    Copy(bound = ""),
    Debug(bound = ""),
    PartialEq(bound = ""),
    Eq(bound = "")
)]
#[derive(CanonicalSerialize, CanonicalDeserialize)]
pub struct Commitment<E: PairingEngine>(
    /// The commitment is a group element.
    pub E::G1Affine,
);

impl_bytes!(Commitment);

impl<E: PairingEngine> ToMinimalBits for Commitment<E> {
    fn to_minimal_bits(&self) -> Vec<bool> {
        self.0.to_minimal_bits()
    }
}

impl<E: PairingEngine> PCCommitment for Commitment<E> {
    #[inline]
    fn empty() -> Self {
        Commitment(E::G1Affine::zero())
    }

    fn has_degree_bound(&self) -> bool {
        false
    }

    fn is_in_correct_subgroup_assuming_on_curve(&self) -> bool {
        self.0.is_in_correct_subgroup_assuming_on_curve()
    }
}

impl<'a, E: PairingEngine> AddAssign<(E::Fr, &'a Commitment<E>)> for Commitment<E> {
    #[inline]
    fn add_assign(&mut self, (f, other): (E::Fr, &'a Commitment<E>)) {
        let mut other = other.0.mul(f).into_projective();
        other.add_assign_mixed(&self.0);
        self.0 = other.into();
    }
}

impl<E: PairingEngine> ToConstraintField<E::Fq> for Commitment<E> {
    fn to_field_elements(&self) -> Result<Vec<E::Fq>, ConstraintFieldError> {
        self.0.to_field_elements()
    }
}

/// `PreparedCommitment` commits to a polynomial and prepares for mul_bits.
#[derive(Derivative)]
#[derivative(
    Default(bound = ""),
    Hash(bound = ""),
    Clone(bound = ""),
    Debug(bound = ""),
    PartialEq(bound = ""),
    Eq(bound = "")
)]
pub struct PreparedCommitment<E: PairingEngine>(
    /// The commitment is a group element.
    pub Vec<E::G1Affine>,
);

impl<E: PairingEngine> PreparedCommitment<E> {
    /// prepare `PreparedCommitment` from `Commitment`
    pub fn prepare(comm: &Commitment<E>) -> Self {
        let mut prepared_comm = Vec::<E::G1Affine>::new();
        let mut cur = E::G1Projective::from(comm.0);

        let supported_bits = E::Fr::size_in_bits();

        for _ in 0..supported_bits {
            prepared_comm.push(cur.into());
            cur.double_in_place();
        }

        Self { 0: prepared_comm }
    }
}

/// `Randomness` hides the polynomial inside a commitment. It is output by `KZG10::commit`.
#[derive(Derivative)]
#[derivative(
    Default(bound = ""),
    Hash(bound = ""),
    Clone(bound = ""),
    Debug(bound = ""),
    PartialEq(bound = ""),
    Eq(bound = "")
)]
#[derive(CanonicalSerialize, CanonicalDeserialize)]
pub struct Randomness<E: PairingEngine> {
    /// For KZG10, the commitment randomness is a random polynomial.
    pub blinding_polynomial: Polynomial<E::Fr>,
}
impl_bytes!(Randomness);

impl<E: PairingEngine> Randomness<E> {
    /// Does `self` provide any hiding properties to the corresponding commitment?
    /// `self.is_hiding() == true` only if the underlying polynomial is non-zero.
    #[inline]
    pub fn is_hiding(&self) -> bool {
        !self.blinding_polynomial.is_zero()
    }

    /// What is the degree of the hiding polynomial for a given hiding bound?
    #[inline]
    pub fn calculate_hiding_polynomial_degree(hiding_bound: usize) -> usize {
        hiding_bound + 1
    }
}

impl<E: PairingEngine> PCRandomness for Randomness<E> {
    fn empty() -> Self {
        Self {
            blinding_polynomial: Polynomial::zero(),
        }
    }

    fn rand<R: RngCore>(hiding_bound: usize, _: bool, rng: &mut R) -> Self {
        let mut randomness = Randomness::empty();
        let hiding_poly_degree = Self::calculate_hiding_polynomial_degree(hiding_bound);
        randomness.blinding_polynomial = Polynomial::rand(hiding_poly_degree, rng);
        randomness
    }
}

impl<'a, E: PairingEngine> Add<&'a Randomness<E>> for Randomness<E> {
    type Output = Self;

    #[inline]
    fn add(mut self, other: &'a Self) -> Self {
        self.blinding_polynomial += &other.blinding_polynomial;
        self
    }
}

impl<'a, E: PairingEngine> Add<(E::Fr, &'a Randomness<E>)> for Randomness<E> {
    type Output = Self;

    #[inline]
    fn add(mut self, other: (E::Fr, &'a Randomness<E>)) -> Self {
        self += other;
        self
    }
}

impl<'a, E: PairingEngine> AddAssign<&'a Randomness<E>> for Randomness<E> {
    #[inline]
    fn add_assign(&mut self, other: &'a Self) {
        self.blinding_polynomial += &other.blinding_polynomial;
    }
}

impl<'a, E: PairingEngine> AddAssign<(E::Fr, &'a Randomness<E>)> for Randomness<E> {
    #[inline]
    fn add_assign(&mut self, (f, other): (E::Fr, &'a Randomness<E>)) {
        self.blinding_polynomial += (f, &other.blinding_polynomial);
    }
}

/// `Proof` is an evaluation proof that is output by `KZG10::open`.
#[derive(Derivative)]
#[derivative(
    Default(bound = ""),
    Hash(bound = ""),
    Clone(bound = ""),
    Copy(bound = ""),
    Debug(bound = ""),
    PartialEq(bound = ""),
    Eq(bound = "")
)]
#[derive(CanonicalSerialize, CanonicalDeserialize)]
pub struct Proof<E: PairingEngine> {
    /// This is a commitment to the witness polynomial; see [KZG10] for more details.
    pub w: E::G1Affine,
    /// This is the evaluation of the random polynomial at the point for which
    /// the evaluation proof was produced.
    pub random_v: Option<E::Fr>,
}
impl_bytes!(Proof);

impl<E: PairingEngine> PCProof for Proof<E> {
    fn is_hiding(&self) -> bool {
        self.random_v.is_some()
    }
}
