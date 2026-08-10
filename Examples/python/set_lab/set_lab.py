"""set_lab — H7+ sets, the honest subset: the acceptance battery.

`self.history` needs exactly: `set(iterable)` construction and `in`
membership on a frozen-after-build set (plus `len` and truthiness, which
are order-blind like membership). EVERYTHING else about sets is loud —
iteration, `add`/`remove`/`pop`, `==`, `sorted(set)` — because a set's
iteration order is hash order in CPython and is never guessed.
Construction deduplicates by value equality under the dict-KEY doctrine
(bool/int identity: `set([1, True])` has len 1).
"""


def member_int(a):
    s = set([1, 2, 3, a])
    return (a in s, 9 in s, len(s))


def member_tuple(a, b):
    # the history shape: membership of tuples (Positions are tuples)
    s = set([(a, "x"), (b, "y")])
    return ((a, "x") in s, (a, "y") in s)


def dedup_bool():
    # CPython: 1 == True, so set([1, True, 0, False, 2]) has 3 elements
    return len(set([1, True, 0, False, 2]))


def from_str(c):
    s = set("hello")
    return (c in s, len(s))


def from_tuple(a):
    s = set((a, a, a + 1))
    return len(s)


def empty_set(a):
    s = set()
    return (a in s, len(s), 1 if s else 0)


def from_gen(n):
    def g():
        i = 0
        while i < n:
            yield i % 3
            i = i + 1
    s = set(g())
    return (0 in s, len(s))


def not_in(a):
    s = set([a])
    return a + 1 not in s


def iter_is_loud(a):
    s = set([a, a + 1])
    t = 0
    for v in s:
        t = t + v
    return t


def sorted_is_loud(a):
    return sorted(set([3, 1, a]))


def unhashable_elem():
    return len(set([[1, 2]]))


def unhashable_probe(a):
    # CPython HASHES the membership probe before any comparison, so an
    # unhashable probe raises — even against a set that could never
    # contain it
    s = set([a])
    return [a] in s
