"""leanpy corpus: A FUNCTION CALLED FROM INSIDE A TOP-LEVEL LOOP sees the
loop's own bindings — the last seam in THE ONE PIPELINE, closed.

Top-level bindings become module globals when the statement they are in
ENDS, so a compound statement the executor delegated WHOLESALE to
`execStmt` held them in the frame and a call made from inside it read
them stale. `scriptFlushCoherent` refused exactly that overlap rather
than answer wrongly. The general `for` now has its own control shell
(mirroring `execStmt`'s dispatch arm for arm — value sequences, the live
heap-list index cursor, the lazy generator cursor — so the TIER is
unchanged and only the publish granularity differs), and this file, which
the guard used to refuse, runs.

`try` and `for … else` are still delegated wholesale and still guarded.
"""

n = 0


def readn():
    return n


for i in [1, 2, 3]:
    n = n + i
    print(readn())

print(n)

for c in "ab":
    print(c, readn())

tot = 0
for k in range(3):
    tot += k
    print(readn(), tot)
