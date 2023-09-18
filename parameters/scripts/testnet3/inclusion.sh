# Generates the inclusion proving and verifying key.

# Inputs: network

cargo run --release --example inclusion testnet3 -- --nocapture || exit

mv inclusion.metadata ../../src/testnet3/resources || exit
mv inclusion.prover.* ~/.aleo/resources || exit
mv inclusion.verifier ../../src/testnet3/resources || exit
