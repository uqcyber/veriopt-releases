#!/bin/bash

isabelle build -d . -v -c semantics

find output/document -type f -name "*.tex" -exec sed -n '/snip/,/endsnip/p' {} + | \
    sed -e 's/isasymlongmapsto/isasymmapsto/g' > "../../papers/cpp-2021/snippets.tex"
