# Net declaration assignment at the E boundary

This clean-room fixture isolates the construct that stops the retained
PicoRV32 source at `wire dbg_mem_valid = mem_valid`.  IEEE 1800-2023 §§6.7
and 10.3 make `wire t = a` a continuous driver: later changes of `a` must
reach `t`, rather than being treated as a one-time storage initializer.

The parser-shaped envelope retains the declaration assignment and the
following `assign`.  The flat E entry reports the exact existing
`decl 't': non-literal initializer outside the M0 tier` refusal, while the
memory entry keeps its generic unsupported-module-member boundary.  No
lowering or substitute execution rule is introduced here.  `check.py`
regenerates the envelope and compares the four source rows against Icarus and
Xcelium.
