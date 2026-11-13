# Canonical-E case in an implicit memory process

This clean-room source retains a one-rank unpacked memory, a time-zero
initializer, and a plain `always @*` body with parser-native `case` selection.
The body reads either memory cell or the scalar default and reactivates when
`sel` or `d` changes, under IEEE 1800-2023 §§9.4.2.2.2 and 12.5. Icarus Verilog
13.0 and readiness-gated Xcelium 24.03-s004 are the pinned oracles.
