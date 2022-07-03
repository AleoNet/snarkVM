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

use console::network::prelude::*;
use snarkvm_curves::{bls12_377::Bls12_377, PairingEngine};

use core::marker::PhantomData;

type Fq = <Bls12_377 as PairingEngine>::Fq;
type Fr = <Bls12_377 as PairingEngine>::Fr;

pub struct UniversalSRS<N: Network> {
    /// The universal SRS parameter.
    srs: snarkvm_algorithms::snark::marlin::UniversalSRS<Bls12_377>,
    /// PhantomData
    _phantom: PhantomData<N>,
}

impl<N: Network> UniversalSRS<N> {
    /// Initializes the universal SRS.
    pub fn new(num_gates: usize) -> Result<Self> {
        // TODO (howardwu): Replace me.
        use snarkvm_algorithms::{
            crypto_hash::PoseidonSponge,
            snark::marlin::{ahp::AHPForR1CS, fiat_shamir, MarlinHidingMode, MarlinSNARK},
            SNARK,
        };

        // TODO (howardwu): Replace me.
        type FS = fiat_shamir::FiatShamirAlgebraicSpongeRng<Fr, Fq, PoseidonSponge<Fq, 6, 1>>;
        type Marlin = MarlinSNARK<Bls12_377, FS, MarlinHidingMode, [Fr]>;

        let mut rng = rand::thread_rng();

        let timer = std::time::Instant::now();
        let max_degree = AHPForR1CS::<Fr, MarlinHidingMode>::max_degree(num_gates, num_gates, num_gates).unwrap();
        let universal_srs = Marlin::universal_setup(&max_degree, &mut rng)?;
        println!("Called universal setup: {} ms", timer.elapsed().as_millis());

        Ok(Self { srs: universal_srs, _phantom: PhantomData })
    }

    /// Returns the function key.
    pub fn function_key(&self, assignment: circuit::Assignment<Fr>) -> Result<FunctionKey<N>> {
        // TODO (howardwu): Replace me.
        use snarkvm_algorithms::{
            crypto_hash::PoseidonSponge,
            snark::marlin::{fiat_shamir, MarlinHidingMode, MarlinSNARK},
        };

        // TODO (howardwu): Replace me.
        type FS = fiat_shamir::FiatShamirAlgebraicSpongeRng<Fr, Fq, PoseidonSponge<Fq, 6, 1>>;
        type Marlin = MarlinSNARK<Bls12_377, FS, MarlinHidingMode, [Fr]>;

        let timer = std::time::Instant::now();
        let (proving_key, verifying_key) = Marlin::circuit_setup(self, &assignment).unwrap();
        println!("Called setup: {} ms", timer.elapsed().as_millis());

        Ok(FunctionKey {
            proving_key: ProvingKey { proving_key, _phantom: PhantomData },
            verifying_key: VerifyingKey { verifying_key, _phantom: PhantomData },
        })
    }
}

impl<N: Network> Deref for UniversalSRS<N> {
    type Target = snarkvm_algorithms::snark::marlin::UniversalSRS<Bls12_377>;

    fn deref(&self) -> &Self::Target {
        &self.srs
    }
}

pub struct Proof<N: Network> {
    /// The proof.
    proof: snarkvm_algorithms::snark::marlin::Proof<Bls12_377>,
    /// PhantomData
    _phantom: PhantomData<N>,
}

impl<N: Network> Deref for Proof<N> {
    type Target = snarkvm_algorithms::snark::marlin::Proof<Bls12_377>;

    fn deref(&self) -> &Self::Target {
        &self.proof
    }
}

pub struct FunctionKey<N: Network> {
    /// The proving key for the function.
    proving_key: ProvingKey<N>,
    /// The verifying key for the function.
    verifying_key: VerifyingKey<N>,
}

pub struct ProvingKey<N: Network> {
    /// The proving key for the function.
    proving_key: snarkvm_algorithms::snark::marlin::CircuitProvingKey<
        Bls12_377,
        snarkvm_algorithms::snark::marlin::MarlinHidingMode,
    >,
    /// PhantomData
    _phantom: PhantomData<N>,
}

impl<N: Network> ProvingKey<N> {
    fn prove<R: Rng + CryptoRng>(&self, assignment: circuit::Assignment<Fr>, rng: &mut R) -> Result<Proof<N>> {
        // TODO (howardwu): Replace me.
        use snarkvm_algorithms::{
            crypto_hash::PoseidonSponge,
            snark::marlin::{fiat_shamir, MarlinHidingMode, MarlinSNARK},
            SNARK,
        };

        // TODO (howardwu): Replace me.
        type FS = fiat_shamir::FiatShamirAlgebraicSpongeRng<Fr, Fq, PoseidonSponge<Fq, 6, 1>>;
        type Marlin = MarlinSNARK<Bls12_377, FS, MarlinHidingMode, [Fr]>;

        let timer = std::time::Instant::now();
        let proof = Marlin::prove_batch(self, std::slice::from_ref(&assignment), rng).unwrap();
        println!("Called prover: {} ms", timer.elapsed().as_millis());

        Ok(Proof { proof, _phantom: PhantomData })
    }
}

impl<N: Network> Deref for ProvingKey<N> {
    type Target = snarkvm_algorithms::snark::marlin::CircuitProvingKey<
        Bls12_377,
        snarkvm_algorithms::snark::marlin::MarlinHidingMode,
    >;

    fn deref(&self) -> &Self::Target {
        &self.proving_key
    }
}

pub struct VerifyingKey<N: Network> {
    /// The verifying key for the function.
    verifying_key: snarkvm_algorithms::snark::marlin::CircuitVerifyingKey<
        Bls12_377,
        snarkvm_algorithms::snark::marlin::MarlinHidingMode,
    >,
    /// PhantomData
    _phantom: PhantomData<N>,
}

impl<N: Network> VerifyingKey<N> {
    fn verify(&self, inputs: &[Fr], proof: Proof<N>) -> bool {
        // TODO (howardwu): Replace me.
        use snarkvm_algorithms::{
            crypto_hash::PoseidonSponge,
            snark::marlin::{fiat_shamir, MarlinHidingMode, MarlinSNARK},
            SNARK,
        };

        // TODO (howardwu): Replace me.
        type FS = fiat_shamir::FiatShamirAlgebraicSpongeRng<Fr, Fq, PoseidonSponge<Fq, 6, 1>>;
        type Marlin = MarlinSNARK<Bls12_377, FS, MarlinHidingMode, [Fr]>;

        let timer = std::time::Instant::now();
        let is_valid = Marlin::verify_batch(self, std::slice::from_ref(&inputs), &*proof).unwrap();
        println!("Called verifier: {} ms", timer.elapsed().as_millis());
        is_valid
    }
}

impl<N: Network> Deref for VerifyingKey<N> {
    type Target = snarkvm_algorithms::snark::marlin::CircuitVerifyingKey<
        Bls12_377,
        snarkvm_algorithms::snark::marlin::MarlinHidingMode,
    >;

    fn deref(&self) -> &Self::Target {
        &self.verifying_key
    }
}
