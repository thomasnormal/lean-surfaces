# leanpy corpus: the namedtuple VALUE tier under module execution —
# ingestion recognition (the benign import and the binds become `pass`),
# construction, field access, tuple equality, and a dict keyed by a tuple
# containing a namedtuple. The first print opens the live suffix, so the
# top-level Move construction runs live (a G1-prefix construction would
# be a poisoned binding — constructor calls are out of the G1 tier).
from collections import namedtuple

Move = namedtuple("Move", "i j prom")
Entry = namedtuple("Entry", "lower upper")


def window(lo, hi):
    e = Entry(lo, hi)
    return e.upper - e.lower


def best_move(i, j):
    tp = {}
    tp[(Move(i, j, ""), 1)] = window(i, j)
    return tp.get((Move(i, j, ""), 1), -1)


print(window(-10, 10))
m = Move(3, 7, "q")
print(m.i, m.j, m.prom)
print(m == (3, 7, "q"))
print(best_move(2, 5))
