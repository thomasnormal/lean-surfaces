# Undriven net beside a source-shaped E memory

This clean-room fixture keeps the parser's parameter-sized memory and the
undriven `wire pcpi_mul_wr;` as separate source constructs.  The net is
observed through `zq`, so the E profile must retain it as a one-bit scalar net
initialized to `z` under IEEE 1800-2023 §6.6.  The memory remains native
`MemState`; no array expansion or source rewrite is used.

`agree.lean` checks the retained `NetSymbol:net-z` metadata, the z-initialized
declaration, and the three-row E trace.  `check.py` compares the same rows
with Icarus Verilog 13.0 and readiness-gated Xcelium 24.03-s004 when licensed.
