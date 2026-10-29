# Severity-task default formatting

IEEE 1800-2023 §20.10 gives `$info`, `$warning`, and `$error` the same
no-format argument conversions as the output tasks. The legacy self-check tier
lowers represented integral arguments to `%d` and source-pure ASCII string
histories to `%s`. Severity output is outside the self-check transcript, while
unsupported or effectful arguments remain loud.
