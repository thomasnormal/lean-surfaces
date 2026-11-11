# Referenced empty task beside source-shaped E memory

This clean-room fixture keeps a referenced, input-only empty task as the
parser's `SubroutineSymbol:empty-task` module marker.  Its call has the
existing empty statement node and must be a no-op; the neighboring
parameter-sized memory remains native `MemState` and receives a normal NBA
write.  Other task forms remain loud.

`agree.lean` checks marker admission and the three-row E trace.  `check.py`
compares those rows with Icarus Verilog 13.0 and readiness-gated Xcelium
24.03-s004 when licensed.
