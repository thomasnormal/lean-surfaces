# Plain `always @*` case latch retained for E

This clean-room source exercises the parser's `ImplicitEventControl` with a
source-shaped plain `case` that has no `default`.  IEEE 1800-2023 §§9.4.2.2
and 12.5 give the process its inferred sensitivity and latch hold when no arm
matches.  The extractor keeps the `AlwaysEvent` marker and the `Case` node;
it does not invent a default arm or lower the case into an `if` chain.

`agree.lean` checks that retained envelope shape and the E memory elaboration
boundary.  The memory executor remains loud for this source event until its
implicit-wait scheduler and latch state are part of E.  `check.py` compares
the source rows with Icarus Verilog 13.0 and readiness-gated Xcelium
24.03-s004 when licensed.  The first sample is recorded separately because
Icarus leaves the implicit waiter asleep at time zero (`q=xxxx`) while
Xcelium samples the settled port connection (`q=0011`); all later rows,
including unmatched x/z selectors and hold behavior, agree.
