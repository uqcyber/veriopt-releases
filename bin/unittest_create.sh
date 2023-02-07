#!/usr/bin/env bash

# path to the GraalVM graal/compiler folder (relative or absolute)
COMPILER=unittest_translations

echo "Generating Isabelle Tests/UnitTests*.thy files..."

if [ "$#" -lt 1 ]
then
    INPUTS=$(ls $COMPILER/unit_*.test)
else
    INPUTS=$(ls "$@")
fi

MAX_LINES=1000
count=9   # so we start with double digits
# Ignore any *.test files that match the IGNORE egrep expression:
TOOBIG="unit_HP_nest02_test|unit_HP_trees01_test|unit_LoopLivenessTest_manyLoops|unit_Test6753639_test"
IGNORE="unit_SubWordReturnTest_testSnippet|unit_DeoptimizeDirectiveTest_inCompiledCode|unit_Test6753639_test_|unit_Thread_yield01|$TOOBIG"


function startoutput {
    count=$((count + 1))
    OUT="Tests/UnitTests${count}.thy"
    echo "Starting output ${OUT}"
    cat "bin/unittest_header.thy" >$OUT
}

function endoutput {
    echo "end" >>$OUT
}


files=$(ls $INPUTS | egrep -v "$IGNORE")
filecount0=$(ls $INPUTS | wc -l)
filecount=$(echo $files | wc -w)
testcount=$(grep '^value ' $files | wc -l)
echo "Building theories from ${testcount} tests in ${filecount} files out of ${filecount0}."

startoutput
for t in $files
do
    cat "$t" >>$OUT
    lines=$(cat $OUT |wc -l)
    if (( $lines > $MAX_LINES ))
    then
        endoutput
        startoutput
    fi
done
endoutput

echo "Now to execute tests with Isabelle, run:"
echo "    ./bin/unittest_run.sh Tests/UnitTests*.thy"

