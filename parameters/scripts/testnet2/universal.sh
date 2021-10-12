# This script will run the outer SNARK setup and move the resulting `.params`
# and `.checksum` files to `params` folder under the `src` directory.
# If the parameter size has changed, you will need to manually update these in each corresponding struct.

cargo run --release --example setup universal testnet2 || exit

mv universal.metadata ../../src/testnet2/resources
mv universal.srs* ../../src/testnet2/resources
