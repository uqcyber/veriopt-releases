#!/bin/bash

isabelle build -d . -v -c semantics

find output/document -type f -name "*.tex" -exec sed -n '/snip/,/endsnip/p' {} + > "../../papers/cpp-2021/snippets.tex"
