#!/usr/bin/env bash

if [ ! -r Tests/UnitTesting.thy ]; then
	echo "Error: this must be run in the 'isabelle' directory, after Tests session has been built."
	exit 1
fi

echo "To see all results, run: isabelle log -v -T Tests.UnitTesting Tests"
echo -n "Tests passed: " && isabelle log -v -T Tests.UnitTesting Tests | grep '^"True"' | wc -l
echo -n "Tests failed: " && isabelle log -v -T Tests.UnitTesting Tests | grep '^"False"' | wc -l
echo "Details of any failures:"
isabelle log -v -T Tests.UnitTesting Tests | grep --before=1 '"False"' 

