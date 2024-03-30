# Generate proving and verifying keys.

# Inputs: program name

cargo run --release --example setup credits mainnet -- --nocapture || exit

mv *.metadata ../../src/mainnet/resources || exit
mv *.prover.* ~/.aleo/resources || exit
mv *.verifier ../../src/mainnet/resources || exit
