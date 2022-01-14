# This script will run the Noop program SNARK setup and move the resulting `.params`
# and `.checksum` files to `params` folder under the `src` directory.
# If the parameter size has changed, you will need to manually update these in each corresponding struct.

RUST_BACKTRACE=1 cargo run --release --example setup noop testnet2 || exit

mv noop.metadata ../../src/testnet2/resources
mv noop.proving ../../src/testnet2/resources
mv noop.verifying ../../src/testnet2/resources
