# Parameter Scripts

These scripts will run the parameter setup programs in the `examples` folder and move the resulting `.params`
and `.checksum` files to `testnet*` folder under the `src` directory.

If the parameter size has changed, you will need to manually update these in each corresponding struct.

To perform the genesis block generation only, run:
```$xslt
./genesis.sh
```
