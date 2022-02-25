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

use core::marker::PhantomData;

use crate::{
    fft::{
        domain::{FFTPrecomputation, IFFTPrecomputation},
        EvaluationDomain,
    },
    polycommit::LabeledPolynomial,
    snark::marlin::{ahp::matrices::MatrixArithmetization, AHPForR1CS, CircuitInfo, MarlinMode, Matrix},
};
use snarkvm_fields::PrimeField;
use snarkvm_utilities::{serialize::*, SerializationError};

#[derive(derivative::Derivative)]
#[derivative(Clone(bound = "F: PrimeField"))]
#[derive(Debug)]
/// The indexed version of the constraint system.
/// This struct contains three kinds of objects:
/// 1) `index_info` is information about the index, such as the size of the
///     public input
/// 2) `{a,b,c}` are the matrices defining the R1CS instance
/// 3) `{a,b,c}_star_arith` are structs containing information about A^*, B^*, and C^*,
/// which are matrices defined as `M^*(i, j) = M(j, i) * u_H(j, j)`.
pub struct Circuit<F: PrimeField, MM: MarlinMode> {
    /// Information about the indexed circuit.
    pub index_info: CircuitInfo<F>,

    /// The A matrix for the R1CS instance
    pub a: Matrix<F>,
    /// The B matrix for the R1CS instance
    pub b: Matrix<F>,
    /// The C matrix for the R1CS instance
    pub c: Matrix<F>,

    /// Joint arithmetization of the A*, B*, and C* matrices.
    pub a_arith: MatrixArithmetization<F>,
    pub b_arith: MatrixArithmetization<F>,
    pub c_arith: MatrixArithmetization<F>,

    pub fft_precomputation: FFTPrecomputation<F>,
    pub ifft_precomputation: IFFTPrecomputation<F>,

    pub(crate) mode: PhantomData<MM>,
}

impl<F: PrimeField, MM: MarlinMode> Circuit<F, MM> {
    /// The maximum degree required to represent polynomials of this index.
    pub fn max_degree(&self) -> usize {
        self.index_info.max_degree::<MM>()
    }

    /// The number of constraints in this R1CS instance.
    pub fn constraint_domain_size(&self) -> usize {
        crate::fft::EvaluationDomain::<F>::new(self.index_info.num_constraints).unwrap().size()
    }

    /// Iterate over the indexed polynomials.
    pub fn iter(&self) -> impl Iterator<Item = &LabeledPolynomial<F>> {
        [
            &self.a_arith.row,
            &self.a_arith.col,
            &self.a_arith.val,
            &self.a_arith.row_col,
            &self.b_arith.row,
            &self.b_arith.col,
            &self.b_arith.val,
            &self.b_arith.row_col,
            &self.c_arith.row,
            &self.c_arith.col,
            &self.c_arith.val,
            &self.c_arith.row_col,
        ]
        .into_iter()
    }
}

impl<F: PrimeField, MM: MarlinMode> CanonicalSerialize for Circuit<F, MM> {
    #[allow(unused_mut, unused_variables)]
    fn serialize<W: Write>(&self, writer: &mut W) -> Result<(), SerializationError> {
        CanonicalSerialize::serialize(&self.index_info, writer)?;
        CanonicalSerialize::serialize(&self.a, writer)?;
        CanonicalSerialize::serialize(&self.b, writer)?;
        CanonicalSerialize::serialize(&self.c, writer)?;
        CanonicalSerialize::serialize(&self.a_arith, writer)?;
        CanonicalSerialize::serialize(&self.b_arith, writer)?;
        CanonicalSerialize::serialize(&self.c_arith, writer)?;
        CanonicalSerialize::serialize(&self.mode, writer)?;
        Ok(())
    }

    #[allow(unused_mut, unused_variables)]
    fn serialized_size(&self) -> usize {
        let mut size = 0;
        size += CanonicalSerialize::serialized_size(&self.index_info);
        size += CanonicalSerialize::serialized_size(&self.a);
        size += CanonicalSerialize::serialized_size(&self.b);
        size += CanonicalSerialize::serialized_size(&self.c);
        size += CanonicalSerialize::serialized_size(&self.a_arith);
        size += CanonicalSerialize::serialized_size(&self.b_arith);
        size += CanonicalSerialize::serialized_size(&self.c_arith);
        size += CanonicalSerialize::serialized_size(&self.mode);
        size
    }

    #[allow(unused_mut, unused_variables)]
    fn serialize_uncompressed<W: Write>(&self, writer: &mut W) -> Result<(), SerializationError> {
        CanonicalSerialize::serialize_uncompressed(&self.index_info, writer)?;
        CanonicalSerialize::serialize_uncompressed(&self.a, writer)?;
        CanonicalSerialize::serialize_uncompressed(&self.b, writer)?;
        CanonicalSerialize::serialize_uncompressed(&self.c, writer)?;
        CanonicalSerialize::serialize_uncompressed(&self.a_arith, writer)?;
        CanonicalSerialize::serialize_uncompressed(&self.b_arith, writer)?;
        CanonicalSerialize::serialize_uncompressed(&self.c_arith, writer)?;
        CanonicalSerialize::serialize_uncompressed(&self.mode, writer)?;
        Ok(())
    }

    #[allow(unused_mut, unused_variables)]
    fn uncompressed_size(&self) -> usize {
        let mut size = 0;
        size += CanonicalSerialize::uncompressed_size(&self.index_info);
        size += CanonicalSerialize::uncompressed_size(&self.a);
        size += CanonicalSerialize::uncompressed_size(&self.b);
        size += CanonicalSerialize::uncompressed_size(&self.c);
        size += CanonicalSerialize::uncompressed_size(&self.a_arith);
        size += CanonicalSerialize::uncompressed_size(&self.b_arith);
        size += CanonicalSerialize::uncompressed_size(&self.c_arith);
        size += CanonicalSerialize::uncompressed_size(&self.mode);
        size
    }
}
impl<F: PrimeField, MM: MarlinMode> CanonicalDeserialize for Circuit<F, MM> {
    #[allow(unused_mut, unused_variables)]
    fn deserialize<R: Read>(reader: &mut R) -> Result<Self, SerializationError> {
        let index_info: CircuitInfo<F> = CanonicalDeserialize::deserialize(reader)?;
        let constraint_domain_size = EvaluationDomain::<F>::compute_size_of_domain(index_info.num_constraints)
            .ok_or(SerializationError::InvalidData)?;
        let non_zero_a_domain_size = EvaluationDomain::<F>::compute_size_of_domain(index_info.num_non_zero_a)
            .ok_or(SerializationError::InvalidData)?;
        let non_zero_b_domain_size = EvaluationDomain::<F>::compute_size_of_domain(index_info.num_non_zero_b)
            .ok_or(SerializationError::InvalidData)?;
        let non_zero_c_domain_size = EvaluationDomain::<F>::compute_size_of_domain(index_info.num_non_zero_c)
            .ok_or(SerializationError::InvalidData)?;

        let (fft_precomputation, ifft_precomputation) = AHPForR1CS::<F, MM>::fft_precomputation(
            constraint_domain_size,
            non_zero_a_domain_size,
            non_zero_b_domain_size,
            non_zero_c_domain_size,
        )
        .ok_or(SerializationError::InvalidData)?;
        Ok(Circuit {
            index_info,
            a: CanonicalDeserialize::deserialize(reader)?,
            b: CanonicalDeserialize::deserialize(reader)?,
            c: CanonicalDeserialize::deserialize(reader)?,
            a_arith: CanonicalDeserialize::deserialize(reader)?,
            b_arith: CanonicalDeserialize::deserialize(reader)?,
            c_arith: CanonicalDeserialize::deserialize(reader)?,
            fft_precomputation,
            ifft_precomputation,
            mode: CanonicalDeserialize::deserialize(reader)?,
        })
    }

    #[allow(unused_mut, unused_variables)]
    fn deserialize_uncompressed<R: Read>(reader: &mut R) -> Result<Self, SerializationError> {
        {
            let index_info: CircuitInfo<F> = CanonicalDeserialize::deserialize_uncompressed(reader)?;
            let constraint_domain_size = EvaluationDomain::<F>::compute_size_of_domain(index_info.num_constraints)
                .ok_or(SerializationError::InvalidData)?;
            let non_zero_a_domain_size = EvaluationDomain::<F>::compute_size_of_domain(index_info.num_non_zero_a)
                .ok_or(SerializationError::InvalidData)?;
            let non_zero_b_domain_size = EvaluationDomain::<F>::compute_size_of_domain(index_info.num_non_zero_b)
                .ok_or(SerializationError::InvalidData)?;
            let non_zero_c_domain_size = EvaluationDomain::<F>::compute_size_of_domain(index_info.num_non_zero_c)
                .ok_or(SerializationError::InvalidData)?;

            let (fft_precomputation, ifft_precomputation) = AHPForR1CS::<F, MM>::fft_precomputation(
                constraint_domain_size,
                non_zero_a_domain_size,
                non_zero_b_domain_size,
                non_zero_c_domain_size,
            )
            .ok_or(SerializationError::InvalidData)?;

            Ok(Circuit {
                index_info,
                a: CanonicalDeserialize::deserialize_uncompressed(reader)?,
                b: CanonicalDeserialize::deserialize_uncompressed(reader)?,
                c: CanonicalDeserialize::deserialize_uncompressed(reader)?,
                a_arith: CanonicalDeserialize::deserialize_uncompressed(reader)?,
                b_arith: CanonicalDeserialize::deserialize_uncompressed(reader)?,
                c_arith: CanonicalDeserialize::deserialize_uncompressed(reader)?,
                fft_precomputation,
                ifft_precomputation,
                mode: CanonicalDeserialize::deserialize_uncompressed(reader)?,
            })
        }
    }
}
