# Generates the inclusion proving and verifying key.

# Inputs: network

cargo run --release --example inclusion testnet -- --nocapture || exit

mv inclusion.metadata ../../src/testnet/resources || exit
mv inclusion.prover.* ~/.aleo/resources || exit
mv inclusion.verifier ../../src/testnet/resources || exit
