# Generate proving and verifying keys.

# Inputs: program name

cargo run --release --example setup credits canary -- --nocapture || exit

mv *.metadata ../../src/canary/resources || exit
mv *.prover.* ~/.aleo/resources || exit
mv *.verifier ../../src/canary/resources || exit
