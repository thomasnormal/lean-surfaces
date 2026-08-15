"""leanpy corpus: a STARRED assignment target is refused — LOUD.

The regression this pins is a silent WRONG ANSWER, not a gap. `unpackSeq`
already refused a non-name target element, but it checked ARITY FIRST, so
the refusal only fired when the arity happened to coincide: `x, *y = [1,2]`
refused (correct), while this file's `x, *y = [1,2,3]` answered
`ValueError: too many values to unpack (expected 2)` and `x, *y = [1]`
answered `not enough values to unpack (expected 2, got 1)` — CPython 3.9.19
binds all three happily (`1` / `[2, 3]` here). The extractor now refuses the
whole statement (`Starred:target`), so the model answers loudly or not at
all.

Real support is designed (docs/backlog.md §Position 2 — a `Stmt.unpackAssign`
constructor) and built on the `starred-displays` branch; this file only
guards the doctrine, and must keep REFUSING until that lands.
"""

x, *y = [1, 2, 3]
print(x)
print(y)
