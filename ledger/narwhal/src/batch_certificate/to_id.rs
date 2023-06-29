// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use super::*;

impl<N: Network> BatchCertificate<N> {
    /// Returns the certificate ID.
    pub fn to_id(&self) -> Result<Field<N>> {
        Self::compute_certificate_id(self.batch_header.batch_id(), &self.signatures)
    }
}

impl<N: Network> BatchCertificate<N> {
    /// Returns the certificate ID.
    pub fn compute_certificate_id(batch_id: Field<N>, signatures: &IndexMap<Signature<N>, i64>) -> Result<Field<N>> {
        let mut preimage = Vec::new();
        // Insert the batch ID.
        preimage.extend_from_slice(&batch_id.to_bytes_le()?);
        // Insert the signatures.
        for (signature, timestamp) in signatures {
            // Insert the signature.
            preimage.extend_from_slice(&signature.to_bytes_le()?);
            // Insert the timestamp.
            preimage.extend_from_slice(&timestamp.to_bytes_le()?);
        }
        // Hash the preimage.
        N::hash_bhp1024(&preimage.to_bits_le())
    }
}
