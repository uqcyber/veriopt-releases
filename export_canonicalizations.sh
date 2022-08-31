#!/bin/bash

isabelle build -vd . NewOptimizations
isabelle export -d . -x "*:optimizations/*.rules" NewOptimizations

