#!/usr/bin/env bash

isabelle build -vD . -P web

# build dependency graph (ignoring Test/ and archive/ folders)
python bin/dependency_graph.py [A-S]*/*.thy Optimizations/*/*.thy
dot -Tpdf -O dependencies.dot
