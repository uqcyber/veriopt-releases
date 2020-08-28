load("@io_bazel_rules_scala//scala:scala.bzl", "scala_library", "scala_binary", "scala_test")

scala_binary(
    name = "code_gen",
    srcs = glob([
        "src/main/scala/**/*.scala",
    ]),
    main_class = "Compiler",
)
