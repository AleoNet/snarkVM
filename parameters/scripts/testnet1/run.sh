# These are dependent on each other.
./noop.sh || exit
./inner.sh || exit

./posw.sh || exit

./genesis.sh || exit
