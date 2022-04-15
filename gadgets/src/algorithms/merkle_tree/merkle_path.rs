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

use itertools::Itertools;
use std::{borrow::Borrow, marker::PhantomData};

use snarkvm_algorithms::{
    merkle_tree::MerklePath,
    traits::{MerkleParameters, CRH},
};
use snarkvm_fields::PrimeField;
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSystem};

use crate::{
    bits::{boolean::Boolean, ToBytesGadget},
    traits::{algorithms::CRHGadget, alloc::AllocGadget, eq::ConditionalEqGadget, select::CondSelectGadget},
    EqGadget,
};

pub struct MerklePathGadget<
    P: MerkleParameters,
    LeafCRHGadget: CRHGadget<P::LeafCRH, F>,
    TwoToOneCRHGadget: CRHGadget<P::TwoToOneCRH, F>,
    F: PrimeField,
> {
    /// `traversal[i]` is 0 (false) iff ith node from bottom to top is left.
    traversal: Vec<Boolean>,
    /// `path[i]` is the entry of sibling of ith node from bottom to top.
    path: Vec<TwoToOneCRHGadget::OutputGadget>,
    leaf_crh: PhantomData<LeafCRHGadget>,
}

impl<
    P: MerkleParameters,
    LeafCRHGadget: CRHGadget<P::LeafCRH, F, OutputGadget = TwoToOneCRHGadget::OutputGadget>,
    TwoToOneCRHGadget: CRHGadget<P::TwoToOneCRH, F>,
    F: PrimeField,
> MerklePathGadget<P, LeafCRHGadget, TwoToOneCRHGadget, F>
{
    pub fn calculate_root<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        leaf_crh: &LeafCRHGadget,
        two_to_one_crh: &TwoToOneCRHGadget,
        leaf: impl ToBytesGadget<F>,
    ) -> Result<TwoToOneCRHGadget::OutputGadget, SynthesisError> {
        let leaf_bytes = leaf.to_bytes(&mut cs.ns(|| "leaf_to_bytes"))?;
        let mut curr_hash = leaf_crh.check_evaluation_gadget(cs.ns(|| "leaf_hash"), leaf_bytes)?;

        // To traverse up a MT, we iterate over the path from bottom to top

        // At any given bit, the bit being 0 indicates our currently hashed value is the left,
        // and the bit being 1 indicates our currently hashed value is on the right.
        // Thus `left_hash` is the sibling if bit is 1, and it's the computed hash if bit is 0
        for (i, (bit, sibling)) in self.traversal.iter().zip_eq(self.path.iter()).enumerate() {
            let left_hash = TwoToOneCRHGadget::OutputGadget::conditionally_select(
                cs.ns(|| format!("cond_select_left_{}", i)),
                bit,
                sibling,
                &curr_hash,
            )?;
            let right_hash = TwoToOneCRHGadget::OutputGadget::conditionally_select(
                cs.ns(|| format!("cond_select_right_{}", i)),
                bit,
                &curr_hash,
                sibling,
            )?;

            curr_hash = hash_inner_node_gadget::<P::TwoToOneCRH, TwoToOneCRHGadget, F, _>(
                &mut cs.ns(|| format!("hash_inner_node_{}", i)),
                two_to_one_crh,
                &left_hash,
                &right_hash,
            )?;
        }

        Ok(curr_hash)
    }

    pub fn update_leaf<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        leaf_crh: &LeafCRHGadget,
        crh: &TwoToOneCRHGadget,
        old_root: &TwoToOneCRHGadget::OutputGadget,
        old_leaf: impl ToBytesGadget<F>,
        new_leaf: impl ToBytesGadget<F>,
    ) -> Result<TwoToOneCRHGadget::OutputGadget, SynthesisError> {
        self.check_membership(cs.ns(|| "check_membership"), leaf_crh, crh, old_root, &old_leaf)?;
        self.calculate_root(cs.ns(|| "calculate_root"), leaf_crh, crh, &new_leaf)
    }

    #[allow(clippy::too_many_arguments)]
    pub fn update_and_check<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        leaf_crh: &LeafCRHGadget,
        crh: &TwoToOneCRHGadget,
        old_root: &TwoToOneCRHGadget::OutputGadget,
        new_root: &TwoToOneCRHGadget::OutputGadget,
        old_leaf: impl ToBytesGadget<F>,
        new_leaf: impl ToBytesGadget<F>,
    ) -> Result<(), SynthesisError> {
        let actual_new_root =
            self.update_leaf(cs.ns(|| "check_membership"), leaf_crh, crh, old_root, &old_leaf, &new_leaf)?;

        actual_new_root.enforce_equal(cs.ns(|| "enforce_equal_roots"), new_root)?;

        Ok(())
    }

    pub fn check_membership<CS: ConstraintSystem<F>>(
        &self,
        cs: CS,
        leaf_crh: &LeafCRHGadget,
        crh: &TwoToOneCRHGadget,
        root: &TwoToOneCRHGadget::OutputGadget,
        leaf: impl ToBytesGadget<F>,
    ) -> Result<(), SynthesisError> {
        self.conditionally_check_membership(cs, leaf_crh, crh, root, leaf, &Boolean::Constant(true))
    }

    pub fn conditionally_check_membership<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        leaf_crh: &LeafCRHGadget,
        crh: &TwoToOneCRHGadget,
        root: &TwoToOneCRHGadget::OutputGadget,
        leaf: impl ToBytesGadget<F>,
        should_enforce: &Boolean,
    ) -> Result<(), SynthesisError> {
        let expected_root = self.calculate_root(cs.ns(|| "calculate_root"), leaf_crh, crh, leaf)?;

        root.conditional_enforce_equal(&mut cs.ns(|| "root_is_eq"), &expected_root, should_enforce)
    }
}

/// Computes a root given `leaves`. Assumes the number of leaves is
/// for a full tree, so it hashes the leaves until there is only one element.
pub fn compute_root<
    TwoToOneCRH: CRH,
    TwoToOneCRHGadget: CRHGadget<TwoToOneCRH, F>,
    F: PrimeField,
    CS: ConstraintSystem<F>,
>(
    mut cs: CS,
    crh: &TwoToOneCRHGadget,
    leaves: &[TwoToOneCRHGadget::OutputGadget],
) -> Result<TwoToOneCRHGadget::OutputGadget, SynthesisError> {
    // Assume the leaves are already hashed.
    let mut current_leaves = leaves.to_vec();
    let mut level = 0;
    // Keep hashing pairs until there is only one element - the root.
    while current_leaves.len() != 1 {
        current_leaves = current_leaves
            .chunks(2)
            .enumerate()
            .map(|(i, left_right)| {
                let inner_hash = hash_inner_node_gadget::<TwoToOneCRH, TwoToOneCRHGadget, F, _>(
                    cs.ns(|| format!("hash left right {} on level {}", i, level)),
                    crh,
                    &left_right[0],
                    &left_right[1],
                );
                inner_hash
            })
            .collect::<Result<Vec<_>, _>>()?;
        level += 1;
    }

    let computed_root = current_leaves[0].clone();
    Ok(computed_root)
}

pub(crate) fn hash_inner_node_gadget<TwoToOneCRH, TwoToOneCRHGadget, F, CS>(
    mut cs: CS,
    crh: &TwoToOneCRHGadget,
    left_child: &TwoToOneCRHGadget::OutputGadget,
    right_child: &TwoToOneCRHGadget::OutputGadget,
) -> Result<TwoToOneCRHGadget::OutputGadget, SynthesisError>
where
    F: PrimeField,
    CS: ConstraintSystem<F>,
    TwoToOneCRH: CRH,
    TwoToOneCRHGadget: CRHGadget<TwoToOneCRH, F>,
{
    let left_bytes = left_child.to_bytes(&mut cs.ns(|| "left_to_bytes"))?;
    let right_bytes = right_child.to_bytes(&mut cs.ns(|| "right_to_bytes"))?;
    let mut bytes = left_bytes;
    bytes.extend_from_slice(&right_bytes);

    crh.check_evaluation_gadget(cs, bytes)
}

impl<P, LeafCRHGadget, TwoToOneCRHGadget, F> AllocGadget<MerklePath<P>, F>
    for MerklePathGadget<P, LeafCRHGadget, TwoToOneCRHGadget, F>
where
    P: MerkleParameters,
    LeafCRHGadget: CRHGadget<P::LeafCRH, F>,
    TwoToOneCRHGadget: CRHGadget<P::TwoToOneCRH, F>,
    F: PrimeField,
{
    fn alloc<Fn, T, CS: ConstraintSystem<F>>(mut cs: CS, value_gen: Fn) -> Result<Self, SynthesisError>
    where
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<MerklePath<P>>,
    {
        let merkle_path = value_gen()?.borrow().clone();

        let mut traversal = vec![];
        for (i, position) in merkle_path.position_list().enumerate() {
            traversal.push(Boolean::alloc(cs.ns(|| format!("alloc_position_{}", i)), || Ok(position))?);
        }

        let mut path = Vec::with_capacity(merkle_path.path.len());
        for (i, node) in merkle_path.path.iter().enumerate() {
            path.push(TwoToOneCRHGadget::OutputGadget::alloc(&mut cs.ns(|| format!("alloc_node_{}", i)), || {
                Ok(*node)
            })?);
        }

        Ok(MerklePathGadget { traversal, path, leaf_crh: PhantomData })
    }

    fn alloc_input<Fn, T, CS: ConstraintSystem<F>>(mut cs: CS, value_gen: Fn) -> Result<Self, SynthesisError>
    where
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<MerklePath<P>>,
    {
        let merkle_path = value_gen()?.borrow().clone();

        let mut traversal = vec![];
        for (i, position) in merkle_path.position_list().enumerate() {
            traversal.push(Boolean::alloc_input(cs.ns(|| format!("alloc_input_position_{}", i)), || Ok(position))?);
        }

        let mut path = Vec::with_capacity(merkle_path.path.len());
        for (i, node) in merkle_path.path.iter().enumerate() {
            path.push(TwoToOneCRHGadget::OutputGadget::alloc_input(
                &mut cs.ns(|| format!("alloc_input_node_{}", i)),
                || Ok(*node),
            )?);
        }

        Ok(MerklePathGadget { traversal, path, leaf_crh: PhantomData })
    }
}
