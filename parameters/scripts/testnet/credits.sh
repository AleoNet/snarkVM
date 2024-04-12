# Generate proving and verifying keys.

# Inputs: program name

cargo run --release --example setup credits testnet -- --nocapture || exit

mv *.metadata ../../src/testnet/resources || exit
mv *.prover.* ~/.aleo/resources || exit
mv *.verifier ../../src/testnet/resources || exit
