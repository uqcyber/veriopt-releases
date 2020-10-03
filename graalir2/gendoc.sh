#!/bin/bash

isabelle build -d . -v -c semantics

find output/document -type f -name "*.tex" \
    -exec sed -n -e '/\\providecommand{\\DefineSnippet}/n' \
        -e '/\\newcommand{\\Snip}/n' \
        -e '/\\newcommand{\\EndSnip}/n' \
        -e '/\\Snip/,/\\EndSnip/p' {} + | \
    sed -e 's/\\Snip{\([^}]*\)}/\\Snip{\1}{/' \
        -e 's/\\EndSnip/}\%EndSnip/' \
        -e 's/isasymhookrightarrow/isasymmapsto/g' \
		> "../../papers/cpp-2021/snippets.tex"

#find output/document -type f -name "*.tex" -exec sed -n '/snip/,/endsnip/p' {} + | \
#    sed -e 's/isasymhookrightarrow/isasymmapsto/g' > "../../papers/cpp-2021/snippets.tex"
