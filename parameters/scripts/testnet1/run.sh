# These are dependent on each other.
./inner.sh || exit

./posw.sh || exit

./genesis.sh || exit
