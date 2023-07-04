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

mod bytes;
mod serialize;
mod string;
mod to_address;
mod to_id;

use crate::{BatchHeader, TransmissionID};
use console::{
    account::{Address, Signature},
    prelude::*,
    types::Field,
};

use core::hash::{Hash, Hasher};
use indexmap::{IndexMap, IndexSet};

#[derive(Clone, PartialEq, Eq)]
pub struct BatchCertificate<N: Network> {
    /// The batch header.
    batch_header: BatchHeader<N>,
    /// The `(signature, timestamp)` pairs for the batch ID from the committee.
    signatures: IndexMap<Signature<N>, i64>,
}

impl<N: Network> BatchCertificate<N> {
    /// Initializes a new batch certificate.
    pub fn from(batch_header: BatchHeader<N>, signatures: IndexMap<Signature<N>, i64>) -> Result<Self> {
        // Ensure the signatures are not empty.
        ensure!(!signatures.is_empty(), "Batch certificate must contain signatures");
        // Verify the signatures are valid.
        for (signature, timestamp) in &signatures {
            let preimage = [batch_header.batch_id(), Field::from_u64(*timestamp as u64)];
            if !signature.verify(&signature.to_address(), &preimage) {
                bail!("Invalid batch certificate signature")
            }
        }
        // Return the batch certificate.
        Ok(Self { batch_header, signatures })
    }

    /// Initializes a new batch certificate.
    pub fn from_unchecked(batch_header: BatchHeader<N>, signatures: IndexMap<Signature<N>, i64>) -> Result<Self> {
        // Ensure the signatures are not empty.
        ensure!(!signatures.is_empty(), "Batch certificate must contain signatures");
        // Return the batch certificate.
        Ok(Self { batch_header, signatures })
    }
}

impl<N: Network> BatchCertificate<N> {
    /// Returns the batch header.
    pub const fn batch_header(&self) -> &BatchHeader<N> {
        &self.batch_header
    }

    /// Returns the batch ID.
    pub const fn batch_id(&self) -> Field<N> {
        self.batch_header.batch_id()
    }

    /// Returns the round.
    pub const fn round(&self) -> u64 {
        self.batch_header.round()
    }

    /// Returns the transmission IDs.
    pub const fn transmission_ids(&self) -> &IndexSet<TransmissionID<N>> {
        self.batch_header.transmission_ids()
    }

    /// Returns the batch certificate IDs for the previous round.
    pub const fn previous_certificate_ids(&self) -> &IndexSet<Field<N>> {
        self.batch_header.previous_certificate_ids()
    }

    /// Returns the timestamps of the batch ID from the committee.
    pub fn timestamps(&self) -> impl '_ + Iterator<Item = i64> {
        self.signatures.values().copied().chain([self.batch_header.timestamp()].into_iter())
    }

    /// Returns the signatures of the batch ID from the committee.
    pub fn signatures(&self) -> impl Iterator<Item = &Signature<N>> {
        self.signatures.keys().chain([self.batch_header.signature()].into_iter())
    }
}

impl<N: Network> Hash for BatchCertificate<N> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.batch_header.batch_id().hash(state);
        (self.signatures.len() as u64).hash(state);
        for signature in &self.signatures {
            signature.hash(state);
        }
    }
}

#[cfg(any(test, feature = "test-helpers"))]
pub mod test_helpers {
    use super::*;
    use console::{account::PrivateKey, network::Testnet3, prelude::TestRng, types::Field};

    use indexmap::IndexSet;

    type CurrentNetwork = Testnet3;

    /// Returns a sample batch certificate, sampled at random.
    pub fn sample_batch_certificate(rng: &mut TestRng) -> BatchCertificate<CurrentNetwork> {
        // Sample a batch header.
        let batch_header = crate::batch_header::test_helpers::sample_batch_header(rng);
        // Sample a list of signatures.
        let mut signatures = IndexMap::with_capacity(5);
        for _ in 0..5 {
            let private_key = PrivateKey::new(rng).unwrap();
            let timestamp = time::OffsetDateTime::now_utc().unix_timestamp();
            let timestamp_field = Field::from_u64(timestamp as u64);
            signatures.insert(private_key.sign(&[batch_header.batch_id(), timestamp_field], rng).unwrap(), timestamp);
        }
        // Return the batch certificate.
        BatchCertificate::from(batch_header, signatures).unwrap()
    }

    /// Returns a list of sample batch certificates, sampled at random.
    pub fn sample_batch_certificates(rng: &mut TestRng) -> IndexSet<BatchCertificate<CurrentNetwork>> {
        // Initialize a sample vector.
        let mut sample = IndexSet::with_capacity(10);
        // Append sample batch certificates.
        for _ in 0..10 {
            sample.insert(sample_batch_certificate(rng));
        }
        // Return the sample vector.
        sample
    }
}
