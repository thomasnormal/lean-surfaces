"""leanpy corpus: DEFINITIONS INTERLEAVED WITH LIVE CODE — the payoff row
of the ordered admission (docs/backlog.md, `defsBoundBefore`).

Every reference here comes textually after the definition it names, which
is the exact condition under which the model's position-independent
definition tables and CPython's sequential binding agree. The blanket
"every def precedes all live code" rule used to refuse this file; the
per-name rule runs it. `call_before_def.py` is the complementary direct
forward-reference row: both runtimes raise `NameError` at the call.

The class is deliberately defined AFTER live output too: its creation is
pure (methods only), so CPython's `class` statement prints nothing and the
model skipping it skips nothing.
"""
print("start")


def double(x):
    return x + x


print(double(4))


class Box:
    def __init__(self, v):
        self.v = v

    def get(self):
        return self.v


def boxed(v):
    b = Box(v)
    return b.get()


print(boxed(double(3)))
print("end")
