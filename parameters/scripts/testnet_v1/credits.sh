# Generate proving and verifying keys.

# Inputs: program name

cargo run --release --example setup credits testnet_v1 -- --nocapture || exit

mv *.metadata ../../src/testnet_v1/resources || exit
mv *.prover.* ~/.aleo/resources || exit
mv *.verifier ../../src/testnet_v1/resources || exit
