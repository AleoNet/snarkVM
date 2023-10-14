# Generate proving and verifying keys.

# Inputs: program name

cargo run --release --example setup credits -- --nocapture || exit

mv *.metadata ../../src/testnet3/resources || exit
mv *.prover.* ~/.aleo/resources || exit
mv *.verifier ../../src/testnet3/resources || exit
