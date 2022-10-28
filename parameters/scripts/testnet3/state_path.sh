# Generate state path proving and verifying key.

# Inputs: network

cargo run --release --example state_path testnet3 -- --nocapture || exit

mv state_path.metadata ../../src/testnet3/resources || exit
mv state_path.prover.* ~/.aleo/resources || exit
mv state_path.verifier.* ~/.aleo/resources || exit
