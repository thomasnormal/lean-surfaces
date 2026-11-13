# Canonical-E case beside memory

This clean-room source retains a one-rank unpacked memory, a time-zero
blocking initializer, and an `always_comb` body whose parser-native `case`
selects memory cells or a scalar default. The rows exercise first-match case
selection and reactivation when the scalar selector and default input change,
under IEEE 1800-2023 §§9.2.2.2 and 12.5. Icarus Verilog 13.0 and readiness-
gated Xcelium 24.03-s004 are the pinned oracles.
