# These are dependent on each other.
./universal.sh || exit
./inner.sh || exit

./posw.sh || exit

./genesis.sh || exit
