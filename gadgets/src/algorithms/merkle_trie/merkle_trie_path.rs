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
    traits::{
        algorithms::CRHGadget,
        alloc::AllocGadget,
        eq::{ConditionalEqGadget, EqGadget},
        select::CondSelectGadget,
    },
    EvaluateLtGadget,
};

pub type Key = Vec<UInt8>;
pub type Value = Vec<UInt8>;

pub struct MerkleTriePathGadget<P: MerkleTrieParameters, HG: CRHGadget<P::H, F>, F: PrimeField> {
    /// `traversal[i]` is the location of the parent node among its siblings.
    traversal: Vec<UInt8>,
    /// `path[i]`is the entry of siblings of ith depth from bottom to top and the number of non-filler siblings.
    path: Vec<Vec<HG::OutputGadget>>,
    /// `parents[i]`is the parent key value pair at the ith depth from bottom to top.
    parents: Vec<(Key, Value)>,
    /// The depth of the key, value pair in the tree. All elements of `traversal`, `path`,
    /// and `parents` past the `depth` index, is zeros.
    depth: UInt8,
}

impl<P: MerkleTrieParameters, HG: CRHGadget<P::H, F>, F: PrimeField> MerkleTriePathGadget<P, HG, F> {
    pub fn calculate_root<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        crh: &HG,
        key: impl ToBytesGadget<F>,
        value: impl ToBytesGadget<F>,
    ) -> Result<HG::OutputGadget, SynthesisError> {
        let empty_child =
            HG::OutputGadget::alloc(&mut cs.ns(|| "empty_child"), || Ok(<P::H as CRH>::Output::default()))?;
        let mut curr_hash = Self::hash_node(cs.ns(|| "leaf_hash"), crh, key, value, &vec![
            empty_child.clone();
            P::MAX_BRANCH
        ])?;

        for (i, (((parent_key, parent_value), position), siblings)) in self
            .parents
            .iter()
            .zip_eq(self.traversal.iter())
            .zip_eq(self.path.iter())
            .enumerate()
        {
            let current_depth = UInt8::alloc(cs.ns(|| format!("depth_{}", i)), || Ok(i as u8))?;

            // Insert the current node into the siblings
            let mut final_siblings = vec![];
            for (j, sibling_root) in siblings.iter().enumerate() {
                let current_sibling_index =
                    UInt8::alloc(cs.ns(|| format!("sibling_index_insert_{}_{}", i, j)), || Ok(j as u8))?;

                // Check if the sibling is a filler and should be added or not.
                let index_is_correct =
                    current_sibling_index.is_eq(cs.ns(|| format!("sibling_is_eq_{}_{}", i, j)), &position)?;

                // Select the sibling based on the given index.
                let selected_sibling = HG::OutputGadget::conditionally_select(
                    cs.ns(|| format!("conditionally_select_siblings_insert_{}_{}", i, j)),
                    &index_is_correct,
                    &curr_hash,
                    &sibling_root,
                )?;

                final_siblings.push(selected_sibling);
            }

            // Create the new hash and select it as valid only if the current depth is less than or equal to the given depth.
            let new_hash = Self::hash_node(
                cs.ns(|| format!("leaf_hash_{}", i)),
                crh,
                parent_key,
                parent_value,
                &final_siblings,
            )?;
            let depth_is_in_range = current_depth.less_than(cs.ns(|| format!("less_than_{}", i)), &self.depth)?;
            let selected_hash = HG::OutputGadget::conditionally_select(
                cs.ns(|| format!("conditionally_select_hash_{}", i)),
                &depth_is_in_range,
                &new_hash,
                &curr_hash,
            )?;
            curr_hash = selected_hash;
        }

        Ok(curr_hash)
    }

    pub(crate) fn hash_node<CS: ConstraintSystem<F>>(
        mut cs: CS,
        crh: &HG,
        key: impl ToBytesGadget<F>,
        value: impl ToBytesGadget<F>,
        child_roots: &Vec<HG::OutputGadget>,
    ) -> Result<HG::OutputGadget, SynthesisError> {
        let mut bytes = vec![]; // TODO (raychu86): Add key to hashing.
        bytes.extend_from_slice(&value.to_bytes(cs.ns(|| "value_to_bytes"))?);

        for (i, child) in child_roots.iter().enumerate() {
            let child_bytes = child.to_bytes(&mut cs.ns(|| format!("leaf_to_bytes_{}", i)))?;
            bytes.extend_from_slice(&child_bytes);
        }

        crh.check_evaluation_gadget(cs, bytes)
    }

    pub fn check_membership<CS: ConstraintSystem<F>>(
        &self,
        cs: CS,
        crh: &HG,
        root: &HG::OutputGadget,
        key: impl ToBytesGadget<F>,
        value: impl ToBytesGadget<F>,
    ) -> Result<(), SynthesisError> {
        self.conditionally_check_membership(cs, crh, root, key, value, &Boolean::Constant(true))
    }

    pub fn conditionally_check_membership<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        crh: &HG,
        root: &HG::OutputGadget,
        key: impl ToBytesGadget<F>,
        value: impl ToBytesGadget<F>,
        should_enforce: &Boolean,
    ) -> Result<(), SynthesisError> {
        let expected_root = self.calculate_root(cs.ns(|| "calculate_root"), crh, key, value)?;

        root.conditional_enforce_equal(&mut cs.ns(|| "root_is_eq"), &expected_root, should_enforce)
    }
}

impl<P, HGadget, F, L> AllocGadget<MerkleTriePath<P, L>, F> for MerkleTriePathGadget<P, HGadget, F>
where
    P: MerkleTrieParameters,
    HGadget: CRHGadget<P::H, F>,
    F: PrimeField,
    L: ToBytes + Clone,
{
    fn alloc<Fn, T, CS: ConstraintSystem<F>>(mut cs: CS, value_gen: Fn) -> Result<Self, SynthesisError>
    where
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<MerkleTriePath<P, L>>,
    {
        let merkle_trie_path = value_gen()?.borrow().clone();

        assert_eq!(merkle_trie_path.parents.len(), merkle_trie_path.path.len());
        assert_eq!(merkle_trie_path.path.len(), merkle_trie_path.traversal.len());

        let mut traversal = Vec::with_capacity(P::MAX_DEPTH);
        for (i, position) in merkle_trie_path.traversal.iter().enumerate() {
            traversal.push(UInt8::alloc(
                cs.ns(|| format!("alloc_traversal_position_{}", i)),
                || Ok(*position as u8),
            )?);
        }

        let filler_sibling = <P::H as CRH>::Output::default();

        let mut path = Vec::with_capacity(P::MAX_DEPTH);
        for (i, sibling_roots) in merkle_trie_path.path.iter().enumerate() {
            let mut siblings = vec![];
            for (j, sibling) in sibling_roots.iter().enumerate() {
                siblings.push(HGadget::OutputGadget::alloc(
                    &mut cs.ns(|| format!("alloc_sibling_{}_{}", i, j)),
                    || Ok(sibling.clone()),
                )?);
            }

            // Add the filler siblings
            for j in sibling_roots.len()..P::MAX_BRANCH - 1 {
                siblings.push(HGadget::OutputGadget::alloc(
                    &mut cs.ns(|| format!("alloc_sibling_{}_{}", i, j)),
                    || Ok(filler_sibling.clone()),
                )?);
            }

            // The final filler, where the calculated node will be placed.
            let final_filler =
                HGadget::OutputGadget::alloc(&mut cs.ns(|| format!("alloc_final_filler_{}", i)), || {
                    Ok(<P::H as CRH>::Output::default())
                })?;
            siblings.insert(merkle_trie_path.traversal[i] as usize, final_filler);

            path.push(siblings);
        }

        let mut parents = Vec::with_capacity(P::MAX_DEPTH);
        for (i, (key, value)) in merkle_trie_path.parents.iter().enumerate() {
            let key_gadget = UInt8::alloc_vec(cs.ns(|| format!("alloc_key_{}", i)), &key)?;
            let value_gadget = match value {
                Some(l) => UInt8::alloc_vec(cs.ns(|| format!("alloc_value_{}", i)), &l.to_bytes_le()?)?,
                None => UInt8::alloc_vec(cs.ns(|| format!("alloc_value_{}", i)), &vec![0u8; P::VALUE_SIZE])?, // TODO (raychu86): Use the size of the value.
            };

            parents.push((key_gadget, value_gadget));
        }

        let depth = UInt8::alloc(cs.ns(|| "alloc_depth"), || Ok(merkle_trie_path.parents.len() as u8))?;

        // Fill `traversal`, `path`, and `parents` to the max depth.

        for i in traversal.len()..P::MAX_DEPTH {
            traversal.push(UInt8::alloc(cs.ns(|| format!("alloc_filler_traversal_{}", i)), || {
                Ok(0)
            })?);
        }

        for i in path.len()..P::MAX_DEPTH {
            let mut siblings = vec![];
            for j in 0..P::MAX_BRANCH {
                siblings.push(HGadget::OutputGadget::alloc(
                    &mut cs.ns(|| format!("alloc_filler_sibling_{}_{}", i, j)),
                    || Ok(<P::H as CRH>::Output::default()),
                )?);
            }
            path.push(siblings);
        }

        for i in parents.len()..P::MAX_DEPTH {
            let key_gadget = UInt8::alloc_vec(cs.ns(|| format!("alloc_filler_key_{}", i)), &vec![0u8; P::KEY_SIZE])?; // TODO (raychu86): Use the size of the key.
            let value_gadget =
                UInt8::alloc_vec(cs.ns(|| format!("alloc_filler_value_{}", i)), &vec![0u8; P::VALUE_SIZE])?; // TODO (raychu86): Use the size of the value.
            parents.push((key_gadget, value_gadget));
        }

        assert_eq!(traversal.len(), P::MAX_DEPTH);
        assert_eq!(path.len(), P::MAX_DEPTH);
        assert_eq!(parents.len(), P::MAX_DEPTH);

        Ok(MerkleTriePathGadget {
            traversal,
            path,
            parents,
            depth,
        })
    }

    fn alloc_input<Fn, T, CS: ConstraintSystem<F>>(_cs: CS, _value_gen: Fn) -> Result<Self, SynthesisError>
    where
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<MerkleTriePath<P, L>>,
    {
        // let merkle_trie_path = value_gen()?.borrow().clone();

        unimplemented!()
    }
}
