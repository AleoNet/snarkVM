# This script will run the outer SNARK setup and move the resulting `.params`
# and `.checksum` files to `params` folder under the `src` directory.
# If the parameter size has changed, you will need to manually update these in each corresponding struct.

RUST_BACKTRACE=1 cargo run --release --example outer_snark testnet2 || exit

mv outer_snark_pk*.params ../../src/testnet2
mv outer_snark_pk.checksum ../../src/testnet2

mv outer_snark_vk.params ../../src/testnet2
mv outer_snark_vk.checksum ../../src/testnet2
