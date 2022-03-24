# These are dependent on each other.
./inner.sh || exit

./input.sh || exit

./output.sh || exit

./value_check.sh || exit

./posw.sh || exit

./genesis.sh || exit
