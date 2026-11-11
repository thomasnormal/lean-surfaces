# Plain `always @*` with a continuous time-zero driver in E

This clean-room fixture isolates the generic IEEE 1800-2023 §§9.2.2.2.2 and
9.4.2.2 shape that blocked the current PicoRV32 E admission: a `wire` read by
plain `always @*` is driven by a continuous assignment at time zero.  The
extractor retains the parser's `ImplicitEventControl` node and its blocking
body; it does not lower the source to `always_comb`.  The ordinary frozen
`Process2` view remains loud for this event node.

The E-core-0 `σ_src` receipt starts the implicit process waiting, runs the
continuous driver and the `always_comb` peer, and re-arms the `@*` body on
each changed input.  It is a receipt for that scheduler choice, not an
exact-equivalence theorem for the first observation.  The four-state rows
cover the first observation and known, x/z input changes.  Icarus reports
`y_star=xxxx` on the first row while Xcelium reports `y_star=0011`; the
remaining rows agree.  This is the time-zero Active-region ordering split
allowed by IEEE 1800-2023 §4.7, so the checker records both tool rows and
does not promote either schedule to the language meaning.

Run the focused proof and simulator comparison with:

```text
lake env lean Examples/system-verilog/sem2/always_star_timezero_e/agree.lean
python3 Examples/system-verilog/sem2/always_star_timezero_e/check.py
```
