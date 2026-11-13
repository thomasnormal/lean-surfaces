# Canonical E one-rank register-file memory

This clean-room fixture is the PicoRV32 `cpuregs` shape: one parameter-sized
unpacked declaration, a run-time read index in a continuous assignment, and a
run-time write index in an `always_ff` nonblocking assignment.  The canonical
executor keeps the declaration as one `MemShape`, evaluates indices at issue
time, and commits the native memory NBA queue.  It does not flatten the array
or add a second memory representation.

The Lean receipt in `agree.lean` runs eleven rows at `N=32`.  It covers the
initial x state, a known write/read, x/z read indices, an x-index write, and an
x-valued write enable.  The rows match Icarus Verilog 13.0 and readiness-gated
Xcelium `xrun(64) 24.03-s004` through `check.py`.

The ordinary `instantiateE2` route still reports the real-design wall
`UnpackedDecl:memory` at `picorv32.v:203`; this branch receipt exercises the
canonical source-shaped memory executor that is intended to remove that wall.
