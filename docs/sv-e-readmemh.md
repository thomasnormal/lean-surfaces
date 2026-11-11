# `$readmemh` in the first E memory profile

The clean-room fixture is
[`Examples/system-verilog/sem2/readmemh_rom/`](../Examples/system-verilog/sem2/readmemh_rom/).
The approved Slang envelope retains the parser's `SystemTask:readmemh` node
and its structured `PReadmemh` record (`file`, whole-array target, and hex
words).  E does not parse the task's diagnostic text and does not rewrite the
task into declaration initializers.

At time zero, a single initial process containing only this structured task
writes the words in source array-label order.  A block containing only
`$readmemh` tasks is admitted as the same source-shaped initial; another
statement, a malformed word, a short file, a missing target, or multiple
initial processes remains a named refusal.  The first E memory state retains
fixed unpacked arrays as `MemState` and fixed-cell declarations as their
source-shaped scalar cells, so the same typed file operation covers both
frontend forms.

IEEE 1800-2023 §§4.7, 6.8 and 9.2.1 determine the time-zero boundary.  The
fixture's continuous `rom[addr]` read is evaluated only after the file write,
with unknown addresses reading the uninitialized/unknown result of the normal
four-state expression evaluator.

`check_e.py` compares five rows against Icarus 13.0 and the readiness-gated
Xcelium 24.03-s004.  The rows are `00→00`, `01→11`, `10→22`, `11→33`, and
`xx→xx`; all match E.
