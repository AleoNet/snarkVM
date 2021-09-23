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

use itertools::Itertools;
use std::borrow::Borrow;

use snarkvm_algorithms::{
    merkle_trie::MerkleTriePath,
    traits::{MerkleTrieParameters, CRH},
};
use snarkvm_fields::PrimeField;
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSystem};
use snarkvm_utilities::ToBytes;

use crate::{
    bits::{boolean::Boolean, ToBytesGadget},
    integers::uint::UInt8,
    traits::{algorithms::CRHGadget, alloc::AllocGadget, eq::ConditionalEqGadget, select::CondSelectGadget},
    EqGadget,
};

pub type Key = Vec<UInt8>;
pub type Value = Vec<UInt8>;

pub struct MerkleTriePathGadget<P: MerkleTrieParameters, HG: CRHGadget<P::H, F>, F: PrimeField> {
    /// `traversal[i]` is the location of the parent node among its siblings.
    traversal: Vec<UInt8>,
    /// `path[i]`is the entry of siblings of ith depth from bottom to top.
    path: Vec<Vec<HG::OutputGadget>>,
    /// `parents[i]`is the parent key value pair at the ith depth from bottom to top.
    parents: Vec<(Key, Value)>,
}

impl<P: MerkleTrieParameters, HG: CRHGadget<P::H, F>, F: PrimeField> MerkleTriePathGadget<P, HG, F> {
    pub fn calculate_root<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        crh: &HG,
        leaf: impl ToBytesGadget<F>,
    ) -> Result<HG::OutputGadget, SynthesisError> {
        // let leaf_bytes = leaf.to_bytes(&mut cs.ns(|| "leaf_to_bytes"))?;
        // let mut curr_hash = crh.check_evaluation_gadget(cs.ns(|| "leaf_hash"), leaf_bytes)?;
        //
        // // To traverse up a MT, we iterate over the path from bottom to top
        //
        // // At any given bit, the bit being 0 indicates our currently hashed value is the left,
        // // and the bit being 1 indicates our currently hashed value is on the right.
        // // Thus `left_hash` is the sibling if bit is 1, and it's the computed hash if bit is 0
        // for (i, (bit, sibling)) in self.traversal.iter().zip_eq(self.path.iter()).enumerate() {
        //     let left_hash = HG::OutputGadget::conditionally_select(
        //         cs.ns(|| format!("cond_select_left_{}", i)),
        //         &bit,
        //         &sibling,
        //         &curr_hash,
        //     )?;
        //     let right_hash = HG::OutputGadget::conditionally_select(
        //         cs.ns(|| format!("cond_select_right_{}", i)),
        //         &bit,
        //         &curr_hash,
        //         &sibling,
        //     )?;
        //
        //     curr_hash = hash_inner_node_gadget::<P::H, HG, F, _>(
        //         &mut cs.ns(|| format!("hash_inner_node_{}", i)),
        //         crh,
        //         &left_hash,
        //         &right_hash,
        //     )?;
        // }
        //
        // Ok(curr_hash)

        unimplemented!()
    }

    pub fn check_membership<CS: ConstraintSystem<F>>(
        &self,
        cs: CS,
        crh: &HG,
        root: &HG::OutputGadget,
        leaf: impl ToBytesGadget<F>,
    ) -> Result<(), SynthesisError> {
        self.conditionally_check_membership(cs, crh, root, leaf, &Boolean::Constant(true))
    }

    pub fn conditionally_check_membership<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        crh: &HG,
        root: &HG::OutputGadget,
        leaf: impl ToBytesGadget<F>,
        should_enforce: &Boolean,
    ) -> Result<(), SynthesisError> {
        let expected_root = self.calculate_root(cs.ns(|| "calculate_root"), crh, leaf)?;

        root.conditional_enforce_equal(&mut cs.ns(|| "root_is_eq"), &expected_root, should_enforce)
    }
}

impl<P, HGadget, F, L> AllocGadget<MerkleTriePath<P, L>, F> for MerkleTriePathGadget<P, HGadget, F>
where
    P: MerkleTrieParameters,
    HGadget: CRHGadget<P::H, F>,
    F: PrimeField,
    L: ToBytes,
{
    fn alloc<Fn, T, CS: ConstraintSystem<F>>(mut cs: CS, value_gen: Fn) -> Result<Self, SynthesisError>
    where
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<MerkleTriePath<P, L>>,
    {
        // let merkle_path = value_gen()?.borrow().clone();
        //
        // let mut traversal = vec![];
        // for (i, position) in merkle_path.position_list().enumerate() {
        //     traversal.push(Boolean::alloc(cs.ns(|| format!("alloc_position_{}", i)), || {
        //         Ok(position)
        //     })?);
        // }
        //
        // let mut path = Vec::with_capacity(merkle_path.path.len());
        // for (i, node) in merkle_path.path.iter().enumerate() {
        //     path.push(HGadget::OutputGadget::alloc(
        //         &mut cs.ns(|| format!("alloc_node_{}", i)),
        //         || Ok(node.clone()),
        //     )?);
        // }
        //
        // Ok(MerkleTriePathGadget { traversal, path })

        unimplemented!()
    }

    fn alloc_input<Fn, T, CS: ConstraintSystem<F>>(mut cs: CS, value_gen: Fn) -> Result<Self, SynthesisError>
    where
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<MerkleTriePath<P, L>>,
    {
        // let merkle_path = value_gen()?.borrow().clone();
        //
        // let mut traversal = vec![];
        // for (i, position) in merkle_path.position_list().enumerate() {
        //     traversal.push(Boolean::alloc_input(
        //         cs.ns(|| format!("alloc_input_position_{}", i)),
        //         || Ok(position),
        //     )?);
        // }
        //
        // let mut path = Vec::with_capacity(merkle_path.path.len());
        // for (i, node) in merkle_path.path.iter().enumerate() {
        //     path.push(HGadget::OutputGadget::alloc_input(
        //         &mut cs.ns(|| format!("alloc_input_node_{}", i)),
        //         || Ok(node.clone()),
        //     )?);
        // }
        //
        // Ok(MerkleTriePathGadget { traversal, path, parents })

        unimplemented!()
    }
}
