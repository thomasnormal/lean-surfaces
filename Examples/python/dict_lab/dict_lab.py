"""Dict-tier laboratory: the H1-proper acceptance behaviors as callable
functions (docs/memory-model.md §H1 acceptance). Every function here backs
differential rows in harness/cases.json; the Lean-side regressions
(low-fuel timeout, exception-state retention, WF) live in spec.lean."""


def alias_write(x):
    # 1: local alias mutation — e and d are the same object.
    d = {"x": 0}
    e = d
    e["x"] = x
    return d["x"]


def mutate(d, k, v):
    d[k] = v


def caller_sees(k, v):
    # 2: callee mutation is visible to the caller (shared world).
    d = {}
    mutate(d, k, v)
    return d[k]


def distinct_literals():
    # 3: two separate literals have different identity (but equal value).
    a = {1: 2}
    b = {1: 2}
    return (a is b, a is a, a == b)


def bool_int_key():
    # 4: True/1 address one entry; the original key object is retained
    # (observable here through the entry count and both reads).
    d = {True: 7}
    d[1] = 9
    return (len(d), d[True], d[1])


def dup_literal_keys():
    # 5: duplicate equal literal keys — first position, last value.
    d = {1: "a", True: "b", 0: "z"}
    return (len(d), d[1], d[0])


def eq_ignores_order():
    # 6: dict equality ignores insertion order.
    a = {1: "x", 2: "y"}
    b = {2: "y", 1: "x"}
    return (a == b, a != b)


def self_cycle_eq():
    # 7: a self-cyclic dict equals itself (identity shortcut).
    d = {}
    d[0] = d
    return d == d


def two_cycles_eq():
    # 8: two corresponding self-cyclic dicts -> RecursionError.
    a = {}
    b = {}
    a[0] = a
    b[0] = b
    return a == b


def unhashable_probe():
    # 9: unhashable membership probe raises on an EMPTY dict.
    d = {}
    return [1] in d


def unhashable_store():
    # 9b: unhashable store key raises (list key).
    d = {}
    d[[1]] = 1
    return 0


def eval_order_rhs():
    # 11a: RHS evaluates before the target primary — d is never bound,
    # but the ZeroDivisionError wins over the NameError.
    d[0] = 1 // 0


def eval_order_key():
    # 11b: target primary evaluates before the subscript — the NameError
    # wins over the ZeroDivisionError.
    e[1 // 0] = 5


def ret_dict():
    # 12a: a dict cannot cross the public boundary (loudly unsupported).
    return {}


def ret_tuple_with_dict():
    # 12b: a ref inside a returned tuple is rejected per referent.
    return (1, {})


def get_hit(k):
    d = {1: 10, "a": 20}
    return d.get(k)


def get_default():
    d = {2: 20}
    return (d.get(1), d.get(1, 5), d.get(2, 99))


def truthiness():
    a = {}
    b = {0: 0}
    r = 0
    if a:
        r = r + 1
    if b:
        r = r + 10
    return (r, not a, not b)


def key_error():
    d = {1: 2}
    return d[9]


def len_in(k):
    d = {1: 2, 3: 4}
    return (len(d), k in d, k not in d, 5 in d)


def tuple_keys():
    d = {(1, 2): "a"}
    return (d[(1, 2)], d.get((True, 2)), (1, 3) in d, (1, 2) in d)


def nested_dicts():
    d = {1: {2: 3}}
    return d[1][2]


def dict_eq_mixed():
    return ({1: 2} == {True: 2}, {} == 0, {1: (2, 3)} == {1: (2, 3)})


def store_exc_state(x):
    # 16 (differential slice): the store lands, then the raise; the public
    # boundary shows the exception (state retention is pinned Lean-side).
    d = {}
    d[1] = x
    return d[1] // 0


def int_is(a, b):
    # identity between two non-None immediates: implementation-defined,
    # loudly out of tier.
    return a is b


def iter_dict():
    # 10: live dict iteration is NOT in the H1 inventory (no snapshot
    # shortcut) — loudly unsupported until the live iterator lands.
    d = {1: 2}
    s = 0
    for k in d:
        s = s + k
    return s


def mate_style():
    # sunfish-flavored: the piece table and the MATE bound expression shape.
    piece = {"P": 100, "N": 280, "B": 320, "R": 479, "Q": 929, "K": 60000}
    return piece["K"] + 10 * piece["Q"]


# pass 5 (docs/memory-model.md "search()'s first blockers"): the dict
# MUTATOR .clear() -- search()'s tp_score.clear() shape.

def clear_len(n):
    d = {1: n, 2: n + 1}
    d.clear()
    return len(d)


def clear_alias(n):
    # aliasing-visible, like every heap mutation
    d = {1: n}
    e = d
    e.clear()
    return len(d)


def clear_get(n):
    d = {1: n}
    d.clear()
    return d.get(1, -7)


def clear_refill(n):
    # clear then store: the search() lifecycle in miniature
    d = {1: n}
    d.clear()
    d[2] = n + 3
    return (len(d), d[2])


def clear_none(n):
    d = {1: n}
    return d.clear() is None


def clear_arity(n):
    d = {1: n}
    return d.clear(2)
