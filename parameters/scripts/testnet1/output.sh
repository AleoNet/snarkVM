# This script will run the output SNARK setup and move the resulting `.params`
# and `.checksum` files to `params` folder under the `src` directory.
# If the parameter size has changed, you will need to manually update these in each corresponding struct.

RUST_BACKTRACE=1 cargo run --release --example setup output testnet1 || exit

mv output.metadata ../../src/testnet1/resources
mv output.proving* ~/.aleo/resources
mv output.verifying ../../src/testnet1/resources
