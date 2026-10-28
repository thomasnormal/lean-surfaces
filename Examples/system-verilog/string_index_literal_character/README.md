# Literal string-index character assignments

IEEE 1800-2023 §6.16 permits a constant-index string byte to receive a
one-byte literal. The legacy self-check extractor replays this source-pure
history for later comparisons while retaining dynamic, out-of-range, timed,
nonblocking, and nonliteral writes as loud targets.
