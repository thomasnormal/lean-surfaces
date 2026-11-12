# Disjoint packed concatenation NBA target

This clean-room Step 11 fixture keeps the parser's source-shaped
`ConcatTarget` in an `always_ff` nonblocking assignment:
`{q[7:4], q[3:0]} <= d`.  IEEE 1800-2023 §10.6 defines the concatenation
assignment's left-to-right packed mapping; the two constant windows are
separate portions of the same packed signal.  The E receipt runs this body in
canonical E-core-1 and compares its four-state rows with Icarus Verilog 13.0
and readiness-gated Xcelium 24.03-s004.
