load("@rules_isabelle//isabelle:test.bzl", "isabelle_test")

isabelle_test(
    name = "isabelle",
    session = "semantics",
    root = "ROOT",
    srcs = glob([
        "*.thy"
    ]) + glob([
        "document/**/*.tex",
        "document/**/*.sty",
    ])
)


# load("@rules_isabelle//isabelle:isabelle.bzl", "isabelle_document", "isabelle_html")

# isabelle_document(
#     name = "isabelle",
#     session = "semantics",
#     root = "ROOT",
#     srcs = glob([
#         "*.thy"
#     ]) + glob([
#         "document/**/*.tex",
#         "document/**/*.sty",
#     ]),
#     packages = ["@bazel_latex//packages:amssymb"]
# )

# isabelle_html(
#     name = "isabelle_html",
#     session = "isabelle",
#     root = "ROOT",
#     srcs = glob([
#         "*.thy"
#     ]) + glob([
#         "document/**/*.tex"
#     ])
# )