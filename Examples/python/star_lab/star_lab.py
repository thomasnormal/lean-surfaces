"""star_lab — starred DISPLAYS, the extractor lowering (checks-only).

`[*a, 3]` and `(1, *a)` are lowered by the extractor into
`list((e1,) + tuple(a) + (e2,))` and `(e1,) + tuple(a) + (e2,)`
(docs/memory-model.md §starred displays): zero new AST kinds, zero
interpreter arms, zero proof arms. `list(...)` appears only on the
OUTSIDE — a fresh heap list is exactly what CPython builds there — and
never as a concatenation operand, where a heap object would refuse.

The loud frontier is pinned by refusal probes: a starred CALL argument,
a set display, a dict receiver, a starred assignment TARGET and a
starred `for` target. Those are separate constructs with separate
prices; only the display position is landed.
"""


def list_tail(k):
    a = [1, 2]
    return [*a, k]


def list_head(k):
    a = [1, 2]
    return [k, *a]


def list_two(k):
    a = [1, 2]
    b = [k]
    return [*a, *b]


def list_only():
    a = [1, 2]
    return [*a]


def tuple_only():
    a = [1, 2]
    return (*a,)


def tuple_head(k):
    t = (1, 2)
    return (k, *t)


def tuple_tail(k):
    t = (1, 2)
    return (*t, k)


def groups(k):
    # two starred pieces and two literal groups: four operands, three `+`
    a = [2, 3]
    return [1, *a, k, *a]


def empty():
    return [*[]]


def from_str(s):
    return [*s]


def from_range(n):
    return [*range(n)]


def from_tuple(k):
    t = (1, 2)
    return [*t, k]


def nested(k):
    a = [1, 2]
    return [[*a], k]


def fresh(k):
    # the display ALLOCATES: `b` is a copy, so appending to it leaves `a`
    # alone — the whole reason `list(...)` is on the outside
    a = [1, 2]
    b = [*a]
    b.append(k)
    return (len(a), len(b), a[0], b[2])


def star_int():
    # CPython: `TypeError: Value after * must be an iterable, not int`;
    # the lowering raises `'int' object is not iterable` from `tuple()`.
    # Same exception CLASS, different message — recorded, not glossed.
    return [*5]


def star_none():
    return [*None]


def pair(x, y):
    return x + y


def star_call():
    # position 3: a starred CALL argument stays refused (`call_unsupported`)
    a = [1, 2]
    return pair(*a)


def star_set():
    # a set display is OUT: `{*a}` is a set, whose order is never guessed
    a = [1, 2]
    return {*a}


def star_dict():
    # `[*d]` is CPython's key iteration; `tuple(d)` refuses on the same
    # order doctrine — loud, not wrong
    d = {"x": 1, "y": 2}
    return [*d]


def star_target():
    # position 2: assignment targets are a separate construct, not landed
    x, *y = [1, 2, 3]
    return (x, y)


def star_for():
    # a starred `for` target: the same construct, the same refusal
    for a, *b in [[1, 2, 3]]:
        return (a, b)
    return None
