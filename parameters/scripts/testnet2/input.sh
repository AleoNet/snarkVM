# This script will run the input SNARK setup and move the resulting `.params`
# and `.checksum` files to `params` folder under the `src` directory.
# If the parameter size has changed, you will need to manually update these in each corresponding struct.

RUST_BACKTRACE=1 cargo run --release --example setup input testnet2 || exit

mv input.metadata ../../src/testnet2/resources
mv input.proving* ~/.aleo/resources
mv input.verifying ../../src/testnet2/resources
