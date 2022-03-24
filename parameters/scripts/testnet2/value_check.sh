# This script will run the value check SNARK setup and move the resulting `.params`
# and `.checksum` files to `params` folder under the `src` directory.
# If the parameter size has changed, you will need to manually update these in each corresponding struct.

RUST_BACKTRACE=1 cargo run --release --example setup value_check testnet2 || exit

mv value_check.metadata ../../src/testnet2/resources
mv value_check.proving* ~/.aleo/resources
mv value_check.verifying ../../src/testnet2/resources
