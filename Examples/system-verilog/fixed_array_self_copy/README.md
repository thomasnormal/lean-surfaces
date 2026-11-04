# Fixed-array blocking self-copy

An exact whole-array blocking assignment to itself is a no-op: every source
cell is already the corresponding destination cell. The self-check surface
therefore erases this assignment while preserving the initialized values.
Sliced, overlapping, nonblocking, timed, dynamic, and effectful copies remain
loud.
