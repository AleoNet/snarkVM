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

use crate::{errors::MerkleError, CRH};
use snarkvm_utilities::{to_bytes_le, ToBytes};

use std::fmt::Debug;

pub trait MerkleParameters: Clone + Debug + Send + Sync {
    type H: CRH;

    const DEPTH: usize;

    /// Setup the MerkleParameters
    fn setup(message: &str) -> Self;

    // TODO (howardwu): TEMPORARY - This is a temporary fix to support ToBytes/FromBytes for
    //  LedgerProof and LocalProof. While it is "safe", it is not performant to deserialize
    //  in such a manual fashion. However, given the extent to which modifying the architecture
    //  of Merkle trees in snarkVM impacts many APIs downstream, this forward-compatible change
    //  is being introduced until a proper refactor can be discussed and implemented.
    //  If you are seeing this message, please be proactive in bringing it up :)
    /// Returns the saved `message` from calling the `MerkleParameters::setup()` function.
    fn setup_message(&self) -> &str;

    /// Returns the collision-resistant hash function used by the Merkle tree.
    fn crh(&self) -> &Self::H;

    /// Returns the hash of a given leaf.
    fn hash_leaf<L: ToBytes>(&self, leaf: &L) -> Result<<Self::H as CRH>::Output, MerkleError> {
        Ok(self.crh().hash(&leaf.to_bytes_le()?)?)
    }

    /// Returns the output hash, given a left and right hash value.
    fn hash_inner_node(
        &self,
        left: &<Self::H as CRH>::Output,
        right: &<Self::H as CRH>::Output,
    ) -> Result<<Self::H as CRH>::Output, MerkleError> {
        Ok(self.crh().hash(&to_bytes_le![left, right]?)?)
    }

    fn hash_empty(&self) -> Result<<Self::H as CRH>::Output, MerkleError> {
        // TODO (howardwu): TEMPORARY - This choice of a 64 byte buffer is a temporary fix.
        //  Previously, the size was `<Self::H as CRH>::INPUT_SIZE_BITS / 8` which was also incorrect.
        //  One needs to define a `LeafCRH` and a `TwoToOneCRH` in order to set proper size expectations.
        //  64 bytes was chosen as a temporary fix, to at least ensure the `TwoToOneCRH` preimage size fits,
        //  however this temporary fix does not technically address the issue in a meaningful sense.
        let empty_buffer = &[0u8; 64];
        Ok(self.crh().hash(&*empty_buffer)?)
    }
}

pub trait MaskedMerkleParameters: MerkleParameters {
    /// Returns the collision-resistant hash function masking parameters used by the Merkle tree.
    fn mask_crh(&self) -> &Self::H;
}
