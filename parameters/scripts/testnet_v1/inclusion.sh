# Generates the inclusion proving and verifying key.

# Inputs: network

cargo run --release --example inclusion testnet_v1 -- --nocapture || exit

mv inclusion.metadata ../../src/testnet_v1/resources || exit
mv inclusion.prover.* ~/.aleo/resources || exit
mv inclusion.verifier ../../src/testnet_v1/resources || exit
