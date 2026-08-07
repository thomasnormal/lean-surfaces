"""leanpy v0 corpus: live suffix mutating a prefix-bound module dict —
the shared-heap path (functions read it AFTER the mutation faithfully
because the heap is one object)."""
tt = {}


def probe(k):
    return tt.get(k, -1)


tt[1] = 11
tt[2] = tt[1] + 1
print(probe(1), probe(2), probe(3), len(tt))
