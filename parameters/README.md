# snarkvm-parameters

[![Crates.io](https://img.shields.io/crates/v/snarkvm-parameters.svg?color=neon)](https://crates.io/crates/snarkvm-parameters)
[![Authors](https://img.shields.io/badge/authors-Aleo-orange.svg)](https://aleo.org)
[![License](https://img.shields.io/badge/License-GPLv3-blue.svg)](./LICENSE.md)

The Aleo parameters.

## Commitment 

### Account Commitment

The Pedersen commitment parameters used to construct an Account View Key from an Account Private Key.

### Local Data Commitment

The Pedersen commtiemnt parameters used to construct local data commitment leaves for the local data Merkle tree.

### Record Commitment

THe Pedersen commitment parameters used to construct record commitments.

## CRH

### Encrypted Record CRH

The Bowe-Hopwood Pedersen CRH parameters used to establish the encrypted record hashes used to verify the validity of the encrypted records.

### Inner Circuit ID CRH

The Bowe-Hopwood Pedersen CRH parameters used to compute the inner circuit ID.

### Ledger Merkle Tree

The Bowe-Hopwood Pedersen CRH parameters used to construct the record commitment Merkle tree. 

### Local Data CRH

The Bowe-Hopwood Pedersen CRH parameters used to create the local data commitment Merkle tree.

### Program Verification Key CRH

The Bowe-Hopwood Pedersen CRH parameters used to establish program IDs by hashing Program SNARK verifying keys.

### Serial Number Nonce CRH

The Bowe-Hopwood Pedersen CRH parameters used to construct the serial number nonces for records.

## Encryption 

### Account Encryption

The Group Encryption parameters used to establish the Account Addresses and encrypt records.

## Signature

## Account Signature

The Schnorr signature parameters used to authorize delegation of transaction generation.

## SNARK

### Inner SNARK

The Groth16 proving key and verifying key for the InnerSNARK.

### Outer SNARK

The Groth16 proving key and verifying key for the OuterSNARK.

### Noop Program SNARK

The GM17 proving key and verifying key for the Noop Program SNARK.

### POSW SNARK

The Marlin proving key and verifying key for the Proof of Succinct Work SNARK.