# Generates the inclusion proving and verifying key.

# Inputs: network

cargo run --release --example inclusion canary -- --nocapture || exit

mv inclusion.metadata ../../src/canary/resources || exit
mv inclusion.prover.* ~/.aleo/resources || exit
mv inclusion.verifier ../../src/canary/resources || exit
