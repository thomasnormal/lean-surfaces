"""leanpy corpus: `while … else` DE-DELEGATED — the last compound the
executor handed to `execStmt` wholesale, given the control shell its
siblings got.

Both exits are pinned here. The `else` block runs when the loop ends by
EXHAUSTION (the test goes falsy) and is SKIPPED when it ends by `break` —
`execWhile`'s covenant, which the shell mirrors arm for arm, so the TIER
is unchanged and only the publish granularity differs.

The point of the shell is the publish: top-level bindings become module
globals when the statement they are in ENDS, so under wholesale
delegation the `readn()`/`readtag()` calls made from inside these loops
read them stale, and `scriptFlushCoherent` refused this whole file rather
than answer wrongly. With the shell, the body's bindings AND the else
block's bindings publish per statement, exactly like `for` and `try`.
"""

n = 0
tag = "start"


def readn():
    return n


def readtag():
    return tag


# else TAKEN: the test goes falsy, so the else block runs. It sees the
# body's last binding, and its own binding is live to the call beside it.
i = 0
while i < 3:
    n = n + i
    print("body", i, readn())
    i = i + 1
else:
    tag = "exhausted"
    print("else", readn(), readtag())

print("after", n, tag)

# else SKIPPED: `break` leaves the loop without running the else block.
j = 0
while j < 3:
    n = n + 10
    print("body2", j, readn())
    if j == 1:
        tag = "broke"
        break
    j = j + 1
else:
    tag = "not reached"
    print("else2 ran, which is wrong")

print("after2", n, tag, readtag())

# the degenerate exhaustion: a test false on entry still runs the else.
while n < 0:
    print("never")
else:
    tag = "entry"
    print("else3", readtag())

print("end", n, tag)
