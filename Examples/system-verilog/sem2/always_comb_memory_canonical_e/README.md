# Canonical-E memory beside `always_comb`

This clean-room source retains a one-rank unpacked memory, an edge NBA write,
and an `always_comb` body that reads a memory cell and a scalar input. The body
runs at time zero and reactivates when the memory cell or scalar inputs change,
following IEEE 1800-2023 §§9.2.2.2 and 9.2.2.2.1. The rows are checked with
Icarus Verilog 13.0 and readiness-gated Xcelium 24.03-s004.
