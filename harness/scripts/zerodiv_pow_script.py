"""leanpy corpus: ZeroDivisionError's SECOND text, pinned end to end.

`0 ** -1` raises ZeroDivisionError like `1 // 0` does, but CPython's text
is different — `0.0 cannot be raised to a negative power`, not `integer
division or modulo by zero`. The model carries both since 2026-08-15
(`PyErr.zeroDivisionPow`, a sibling constructor rather than a payload,
docs/backlog.md §the payload-free constructors), so the whole
`ZeroDivisionError: …` line must agree with the oracle here — and
`script_corpus.py` enforces the line whenever the model carries a message,
which makes this row the exact-match guard for the message step.
"""

print("before")
x = 0 ** -1
print("after")
