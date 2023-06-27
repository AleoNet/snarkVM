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

use console::{account::Signature, prelude::*, types::Field};

#[derive(Clone, PartialEq, Eq)]
pub struct BatchCertificate<N: Network> {
    /// The batch ID.
    batch_id: Field<N>,
    /// The `signatures` of the batch ID from the committee.
    signatures: Vec<Signature<N>>,
}

impl<N: Network> BatchCertificate<N> {
    /// Initializes a new batch certificate.
    pub fn new(batch_id: Field<N>, signatures: Vec<Signature<N>>) -> Result<Self> {
        // Ensure the signatures are not empty.
        ensure!(!signatures.is_empty(), "Batch certificate must contain signatures");
        // Return the batch certificate.
        Ok(Self { batch_id, signatures })
    }

    /// Returns the batch ID.
    pub const fn batch_id(&self) -> &Field<N> {
        &self.batch_id
    }

    /// Returns the signatures of the batch ID from the committee.
    pub const fn signatures(&self) -> &Vec<Signature<N>> {
        &self.signatures
    }
}

#[cfg(test)]
pub(crate) mod test_helpers {
    use super::*;
    use console::{
        account::PrivateKey,
        network::Testnet3,
        prelude::{TestRng, Uniform},
        types::Field,
    };

    type CurrentNetwork = Testnet3;

    /// Returns a sample batch certificate, sampled at random.
    pub(crate) fn sample_batch_certificate(rng: &mut TestRng) -> BatchCertificate<CurrentNetwork> {
        // Sample a batch ID.
        let batch_id = Field::rand(rng);
        // Sample a list of signatures.
        let mut signatures = Vec::with_capacity(5);
        for _ in 0..5 {
            let private_key = PrivateKey::new(rng).unwrap();
            signatures.push(private_key.sign(&[batch_id], rng).unwrap());
        }
        // Return the batch certificate.
        BatchCertificate::new(batch_id, signatures).unwrap()
    }

    /// Returns a list of sample batch certificates, sampled at random.
    pub(crate) fn sample_batch_certificates(rng: &mut TestRng) -> Vec<BatchCertificate<CurrentNetwork>> {
        // Initialize a sample vector.
        let mut sample = Vec::with_capacity(10);
        // Append sample batch certificates.
        for _ in 0..10 {
            sample.push(sample_batch_certificate(rng));
        }
        // Return the sample vector.
        sample
    }
}
