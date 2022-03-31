#!/usr/bin/env bash

isabelle build -vD . -P web

# build dependency graph
python bin/dependency_graph.py [A-S]*/*.thy
dot -Tpdf -O dependencies.dot
