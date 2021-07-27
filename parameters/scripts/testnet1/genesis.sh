# This script will run the transaction and block generation programs in the `examples` folder and move the resulting `.genesis` files
# to their respective folders under the `src` directory.
# If the transaction size or checksum has changed, you will need to manually update these in each corresponding struct.

# Generate transactions

# Inputs: recipient address, amount, genesis filepath, transaction filepath

cargo run --release --example genesis aleo17gyptxtlh5vq3yvr3wd2v3x7zz23s49eteep4zj785khhcttkgysss2y0t 100 block_header.genesis transaction_1.genesis || exit

mv transaction_1.genesis ../../src/testnet1/genesis || exit

mv block_header.genesis ../../src/testnet1/genesis || exit
