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

#![forbid(unsafe_code)]
#![warn(clippy::cast_possible_truncation)]

mod bytes;
mod serialize;
mod string;

use console::{
    account::{Address, Signature},
    prelude::*,
    types::Field,
};
use narwhal_batch_certificate::BatchCertificate;
use narwhal_compact_batch_header::CompactBatchHeader;
use narwhal_transmission_id::TransmissionType;

use core::hash::{Hash, Hasher};
use indexmap::{IndexMap, IndexSet};

#[derive(Clone, PartialEq, Eq)]
pub struct CompactBatchCertificate<N: Network> {
    /// The certificate ID.
    certificate_id: Field<N>,
    /// The compact batch header.
    compact_batch_header: CompactBatchHeader<N>,
    /// The `(signature, timestamp)` pairs for the batch ID from the committee.
    signatures: IndexMap<Signature<N>, i64>,
}

impl<N: Network> CompactBatchCertificate<N> {
    /// Initializes a new compact batch certificate.
    pub fn new(
        compact_batch_certificate: CompactBatchHeader<N>,
        signatures: IndexMap<Signature<N>, i64>,
    ) -> Result<Self> {
        // Compute the certificate ID.
        let certificate_id = Self::compute_certificate_id(compact_batch_certificate.batch_id(), &signatures)?;
        // Return the compact batch certificate.
        Self::from(certificate_id, compact_batch_certificate, signatures)
    }

    /// Initializes a new compact batch certificate.
    pub fn from(
        certificate_id: Field<N>,
        compact_batch_header: CompactBatchHeader<N>,
        signatures: IndexMap<Signature<N>, i64>,
    ) -> Result<Self> {
        // Compute the certificate ID.
        if certificate_id != Self::compute_certificate_id(compact_batch_header.batch_id(), &signatures)? {
            bail!("Invalid batch certificate ID")
        }
        // Verify the signatures are valid.
        for (signature, timestamp) in &signatures {
            let preimage = [compact_batch_header.batch_id(), Field::from_u64(*timestamp as u64)];
            if !signature.verify(&signature.to_address(), &preimage) {
                bail!("Invalid compact batch certificate signature")
            }
        }
        // Return the compact batch certificate.
        Self::from_unchecked(certificate_id, compact_batch_header, signatures)
    }

    /// Initializes a new compact batch certificate.
    pub fn from_unchecked(
        certificate_id: Field<N>,
        compact_batch_header: CompactBatchHeader<N>,
        signatures: IndexMap<Signature<N>, i64>,
    ) -> Result<Self> {
        // Ensure the signatures are not empty.
        ensure!(!signatures.is_empty(), "Batch certificate must contain signatures");
        // Return the compact batch certificate.
        Ok(Self { certificate_id, compact_batch_header, signatures })
    }

    /// Initializes a new compact batch certificate from a batch certificate.
    pub fn from_batch_certificate(batch_certificate: &BatchCertificate<N>) -> Result<Self> {
        // Construct the compact batch header.
        let compact_batch_header = CompactBatchHeader::from_batch_header(batch_certificate.batch_header())?;

        // Construct the signatures.
        let signatures = batch_certificate
            .signatures()
            .zip_eq(batch_certificate.timestamps())
            .map(|(signature, timestamp)| (*signature, timestamp))
            .collect::<IndexMap<_, _>>();

        Self::from(batch_certificate.certificate_id(), compact_batch_header, signatures)
    }
}

impl<N: Network> CompactBatchCertificate<N> {
    /// Returns the certificate ID.
    pub const fn certificate_id(&self) -> Field<N> {
        self.certificate_id
    }

    /// Returns the compact batch header.
    pub const fn compact_batch_header(&self) -> &CompactBatchHeader<N> {
        &self.compact_batch_header
    }

    /// Returns the batch ID.
    pub const fn batch_id(&self) -> Field<N> {
        self.compact_batch_header.batch_id()
    }

    /// Returns the author.
    pub const fn author(&self) -> Address<N> {
        self.compact_batch_header.author()
    }

    /// Returns the round.
    pub const fn round(&self) -> u64 {
        self.compact_batch_header.round()
    }

    /// Returns the transmission IDs.
    pub const fn transmission_ids_map(&self) -> &IndexSet<(TransmissionType, u32)> {
        self.compact_batch_header.transmission_ids_map()
    }

    /// Returns the batch certificate IDs for the previous round.
    pub const fn previous_certificate_ids(&self) -> &IndexSet<Field<N>> {
        self.compact_batch_header.previous_certificate_ids()
    }

    /// Returns the median timestamp of the batch ID from the committee.
    pub fn median_timestamp(&self) -> i64 {
        let mut timestamps =
            self.timestamps().chain([self.compact_batch_header.timestamp()].into_iter()).collect::<Vec<_>>();
        timestamps.sort_unstable();
        timestamps[timestamps.len() / 2]
    }

    /// Returns the timestamps of the batch ID from the committee.
    pub fn timestamps(&self) -> impl '_ + ExactSizeIterator<Item = i64> {
        self.signatures.values().copied()
    }

    /// Returns the signatures of the batch ID from the committee.
    pub fn signatures(&self) -> impl ExactSizeIterator<Item = &Signature<N>> {
        self.signatures.keys()
    }
}

impl<N: Network> Hash for CompactBatchCertificate<N> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.compact_batch_header.batch_id().hash(state);
        (self.signatures.len() as u64).hash(state);
        for signature in &self.signatures {
            signature.hash(state);
        }
    }
}

impl<N: Network> CompactBatchCertificate<N> {
    /// Returns the certificate ID.
    pub fn compute_certificate_id(batch_id: Field<N>, signatures: &IndexMap<Signature<N>, i64>) -> Result<Field<N>> {
        let mut preimage = Vec::new();
        // Insert the batch ID.
        batch_id.write_le(&mut preimage)?;
        // Insert the signatures.
        for (signature, timestamp) in signatures {
            // Insert the signature.
            signature.write_le(&mut preimage)?;
            // Insert the timestamp.
            timestamp.write_le(&mut preimage)?;
        }
        // Hash the preimage.
        N::hash_bhp1024(&preimage.to_bits_le())
    }
}

#[cfg(any(test, feature = "test-helpers"))]
pub mod test_helpers {
    use super::*;
    use console::{account::PrivateKey, network::Testnet3, prelude::TestRng, types::Field};

    use indexmap::IndexSet;

    type CurrentNetwork = Testnet3;

    /// Returns a sample compact batch certificate, sampled at random.
    pub fn sample_compact_batch_certificate(rng: &mut TestRng) -> CompactBatchCertificate<CurrentNetwork> {
        sample_compact_batch_certificate_for_round(rng.gen(), rng)
    }

    /// Returns a sample compact batch certificate with a given round; the rest is sampled at random.
    pub fn sample_compact_batch_certificate_for_round(
        round: u64,
        rng: &mut TestRng,
    ) -> CompactBatchCertificate<CurrentNetwork> {
        // Sample certificate IDs.
        let certificate_ids = (0..10).map(|_| Field::<CurrentNetwork>::rand(rng)).collect::<IndexSet<_>>();
        // Return the batch certificate.
        sample_compact_batch_certificate_for_round_with_previous_certificate_ids(round, certificate_ids, rng)
    }

    /// Returns a sample compact batch certificate with a given round; the rest is sampled at random.
    pub fn sample_compact_batch_certificate_for_round_with_previous_certificate_ids(
        round: u64,
        previous_certificate_ids: IndexSet<Field<CurrentNetwork>>,
        rng: &mut TestRng,
    ) -> CompactBatchCertificate<CurrentNetwork> {
        // Sample a batch header.
        let batch_header =
            narwhal_compact_batch_header::test_helpers::sample_compact_batch_header_for_round_with_previous_certificate_ids(
                round,
                previous_certificate_ids,
                rng,
            );
        // Sample a list of signatures.
        let mut signatures = IndexMap::with_capacity(5);
        for _ in 0..5 {
            let private_key = PrivateKey::new(rng).unwrap();
            let timestamp = time::OffsetDateTime::now_utc().unix_timestamp();
            let timestamp_field = Field::from_u64(timestamp as u64);
            signatures.insert(private_key.sign(&[batch_header.batch_id(), timestamp_field], rng).unwrap(), timestamp);
        }
        // Return the compact batch certificate.
        CompactBatchCertificate::new(batch_header, signatures).unwrap()
    }

    /// Returns a list of sample compact batch certificates, sampled at random.
    pub fn sample_compact_batch_certificates(rng: &mut TestRng) -> IndexSet<CompactBatchCertificate<CurrentNetwork>> {
        // Initialize a sample vector.
        let mut sample = IndexSet::with_capacity(10);
        // Append sample compact batch certificates.
        for _ in 0..10 {
            sample.insert(sample_compact_batch_certificate(rng));
        }
        // Return the sample vector.
        sample
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;

    #[test]
    fn test_from_batch_certificate() {
        let rng = &mut TestRng::default();

        // Sample batch certificates.
        let batch_certificates = narwhal_batch_certificate::test_helpers::sample_batch_certificates(rng);

        for batch_certificate in batch_certificates {
            // Convert the batch certificate to a compact batch certificate.
            let compact_batch_certificate =
                CompactBatchCertificate::from_batch_certificate(&batch_certificate).unwrap();

            // Ensure that the compact batch header is correct.
            let expected_compact_batch_header =
                CompactBatchHeader::from_batch_header(batch_certificate.batch_header()).unwrap();
            assert_eq!(compact_batch_certificate.compact_batch_header(), &expected_compact_batch_header);

            // Ensure that the signatures and timestamps are correct.
            for (expected_signature, signature) in
                batch_certificate.signatures().zip_eq(compact_batch_certificate.signatures())
            {
                assert_eq!(expected_signature, signature);
            }
            for (expected_timestamp, timestamp) in
                batch_certificate.timestamps().zip_eq(compact_batch_certificate.timestamps())
            {
                assert_eq!(expected_timestamp, timestamp);
            }
        }
    }
}
