# E memory and always_comb boundary

This clean-room design keeps an unpacked memory beside an `always_comb` process.
The current first memory profile refuses `always_comb` at admission, preserving a
named boundary until its scheduler is modeled. The source rows are checked with
Icarus Verilog 13.0 and readiness-gated Xcelium 24.03-s004.
