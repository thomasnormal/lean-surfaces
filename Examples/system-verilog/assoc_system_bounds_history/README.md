# System associative-array dimension bounds

IEEE 1800-2023 §20.7 defines `$left`, `$right`, `$low`, `$high`,
`$increment`, and `$size` for integral-key associative arrays.  The self-check
tier replays the finite literal-key presence history, including key deletion,
to return exact populated bounds and the fixed integral-index metadata.
Dynamic keys, empty `$low`/`$high` unknown-result cases, aliases, controls, and
timed histories remain loud.
