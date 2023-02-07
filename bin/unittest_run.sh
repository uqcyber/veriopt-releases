#!/usr/bin/env bash

if [ "$#" -lt 1 ]; then
	echo "Usage: $0 Tests/UnitTests*.thy"
	echo "Note: this must be run in the 'isabelle' directory, after unittest_create.sh"
	exit 1
fi

echo "Running tests through Isabelle..."

for f in "$@"
do
    echo "========== $f =========="
    cp "$f" Tests/UnitTesting.thy
    time isabelle build -d . -v Tests
    ./bin/unittest_results.sh >"${f%.thy}.log"
    ./bin/unittest_results.sh 
done
