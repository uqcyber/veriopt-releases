#!/usr/bin/env bash
LOGFILES=Tests/UnitTests*.log

if ls $LOGFILES >/dev/null
then
    echo "$(ls Tests/UnitTests*.thy |wc -l) test theory files"
    echo "$(ls $LOGFILES |wc -l) test output log files"
    grep 'Tests passed' $LOGFILES | awk '{s+=$3} END{print s,"tests passed"}'
    grep 'Tests failed' $LOGFILES | awk '{s+=$3} END{print s,"tests failed"}'
else
    echo "No Tests/UnitTests*.log output files.  Try bin/unittest_run.sh first."
fi

