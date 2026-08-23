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


def unhashable_in_tuple():
    # 9c: CPython names the OFFENDING COMPONENT, not the key --
    # `tuple.__hash__` hashes its elements and the first to raise is the
    # one whose message escapes. The model used to say 'tuple'.
    return {(1, [2]): 0}


def unhashable_nested():
    # the search is depth-first, left to right
    return {(1, (2, [3])): 0}


def unhashable_tuple_read():
    # the same key on the READ path
    d = {}
    return d[(1, [2])]


# §L53 rung 3b (docs/memory-model.md paragraph "dict iteration"): the
# DRAINING consumers over a dict's KEYS. They are sound where the live
# cursor is delicate for one structural reason -- they consume the keys
# with NO user code running in between, so not one of the three mutation
# regimes the census measured can arise inside them. Order is CPython's
# specified insertion order, which the entries array already is.


def keys_tuple(a):
    # ORDER-OBSERVING: the keys come out in insertion order, not sorted
    d = {3: "c", 1: "a", a: "z"}
    return tuple(d)


def keys_list_first(a):
    # list() allocates; index it rather than returning the heap object
    d = {3: "c", 1: "a", a: "z"}
    return list(d)[0]


def keys_list_len(a):
    d = {3: "c", 1: "a", a: "z"}
    return len(list(d))


def keys_star(a):
    # `[*d]` is CPython's key iteration
    d = {3: "c", 1: "a", a: "z"}
    return tuple([*d])


def keys_overwrite_keeps_position(a):
    # an overwrite keeps the key's ORIGINAL position (measured)
    d = {3: "c", 1: "a"}
    d[3] = "zz"
    d[a] = "q"
    return tuple(d)


def keys_sorted(a):
    d = {3: 0, 1: 0, a: 0}
    return tuple(sorted(d))


def keys_sum(a):
    d = {3: 0, 1: 0, a: 0}
    return sum(d)


def keys_max(a):
    d = {3: 0, 1: 0, a: 0}
    return max(d)


def keys_min(a):
    d = {3: 0, 1: 0, a: 0}
    return min(d)


def keys_max_empty():
    # the empty-sequence ValueError still comes from the shared arm
    d = {}
    return max(d)


def keys_any(a):
    d = {0: "x", a: "y"}
    return any(d)


def keys_all(a):
    d = {0: "x", a: "y"}
    return all(d)


def keys_set_len(a):
    # set() over the keys: already distinct, and set membership is
    # order-blind, so nothing about order is claimed
    d = {3: 0, 1: 0, a: 0}
    return len(set(d))


def keys_str_keys(a):
    # non-int keys go through the generic ordering path, not asIntList
    d = {"b": 1, "a": 2}
    return tuple(sorted(d)) + (a,)


def keys_bool_int_collision(a):
    # the dict-key doctrine: True and 1 are the SAME key, first key wins
    d = {True: "x", 1: "y", a: "z"}
    return tuple(d)


def keys_empty():
    d = {}
    return tuple(d)


def keys_for_live_cursor(a):
    # THE TRUNK/REBUILD SPLIT ROW. Written in rung 3b as
    # `keys_for_is_still_loud`, when the live cursor was a separate inch; inch
    # 3a landed it on the MONADIC definition only, so the name asserted
    # something that stopped being true. It now names the CONSTRUCT instead of
    # a verdict, which is the durable choice: the trunk refuses this by the
    # no-backwards-compat ruling and the rebuild runs it, and
    # harness/monadic_gate.py's OPENED table is where CPython adjudicates
    # between them.
    d = {1: a}
    t = 0
    for k in d:
        t = t + k
    return t


# §3c-i-b: dict VIEWS in CONSUMING-ARGUMENT position. Every row below is
# written in the REAL source spelling -- `d.keys()`, not the synthetic
# `<dictkeys>(d)` that ingestion rewrites it to -- because CPython sees the
# source text and the rewrite is exactly what is under test. A row spelled in
# the lowered form would test the evaluator and skip the pass that produced it.


def view_keys_tuple(a):
    d = {3: "c", 1: "a", a: "z"}
    return tuple(d.keys())


def view_values_sorted(a):
    d = {3: "c", 1: "a", a: "z"}
    return tuple(sorted(d.values()))


def view_items_first(a):
    d = {3: "c", 1: a}
    return list(d.items())[0]


def view_items_len(a):
    d = {3: "c", 1: "a", a: "z"}
    return len(list(d.items()))


def view_values_sum(a):
    d = {3: 0, 1: 0, a: 5}
    return sum(d.values())


def view_keys_len(a):
    d = {3: 0, 1: 0, a: 5}
    return len(d.keys())


def view_keys_any(a):
    d = {0: "x", a: "y"}
    return any(d.keys())


def view_keys_max(a):
    d = {3: 0, 1: 0, a: 0}
    return max(d.keys())


def view_escape_still_loud(a):
    # THE BOUNDARY. Binding the view is not a consuming position, so ingestion
    # does not rewrite it and the tier still refuses -- which is what keeps the
    # rewrite's snapshot honest (CPython answers 1 here).
    d = {1: a}
    k = d.keys()
    return len(list(k))


def view_arg_not_alone_still_loud(a):
    # a view beside another argument is not the recognised shape either
    d = {1: a}
    return len(list(d.keys())[0:1])


# §3c-i-c: `enumerate(d)` -- the KEY cursor with an index. It is not a loop
# the interpreter drives but an OBJECT the loop consumes: `enumerate` builds a
# generator frame and every consumer reaches it through the stepper. The rows
# below are the four that pin the behaviour CPython actually has.


def enum_dict_index(a):
    d = {3: 0, 1: 0, a: 0}
    t = 0
    for i, k in enumerate(d):
        t = t + i * k
    return t


def enum_dict_start(a):
    d = {3: 0, 1: 0, a: 0}
    t = 0
    for i, k in enumerate(d, 5):
        t = t + i
    return t


def enum_dict_start_negative(a):
    # the START is an `int`, never a `Nat` -- CPython counts up from -3
    d = {3: 0, a: 0}
    t = 0
    for i, k in enumerate(d, -3):
        t = t + i
    return t


def enum_dict_bind_then_grow(a):
    # THE RULED DELTA (docs/backlog/python-completeness.md
    # 2026-08-23-pycomplete-13, ruling (c)). Binding an enumerate over a dict
    # and then GROWING that dict is SILENT: CPython's guard is on the STEP,
    # not on the bind, so this returns 1. A model that guarded at the bind
    # would raise here and be wrong; a model that SNAPSHOTTED would be wrong
    # at `enum_dict_grow_is_loud` instead. The pair is what makes the ruling
    # falsifiable.
    d = {1: a}
    e = enumerate(d)
    d[2] = 9
    return 1


def enum_dict_grow_then_step(a):
    # ...and STEPPING after the growth raises CPython's RuntimeError. The tier
    # REPRODUCES that rather than refusing it, exactly as `dict.grow-during-iter`
    # already does for the bare cursor -- the size guard was faithful before
    # this inch and this frame inherits it. Named for the CONSTRUCT, not for a
    # verdict: the verdict is the census's to record.
    d = {1: a}
    e = enumerate(d)
    d[2] = 9
    return next(e)[0]


# §del: `del d[k]`, which ingestion lowers to `<dictdel>(d, k)`. The four churn
# rows below are the MEASURED shapes from
# docs/backlog/python-completeness.md 2026-08-23-pycomplete-15: the same-size
# key-set churn regime is NOT guessable (some shapes raise CPython's second
# RuntimeError, some complete silently, and what separates them is the
# entries-array layout), so the tier REFUSES it. Deletion is what makes that
# regime reachable at all, which is why the rows land with this inch.


def del_key(a):
    d = {1: a, 2: 5}
    del d[1]
    return len(d)


def del_then_reinsert_order(a):
    # deletion does NOT hold the slot: reinsertion APPENDS
    d = {1: a, 2: 5, 3: 6}
    del d[2]
    d[2] = 9
    t = 0
    for k in d:
        t = t * 10 + k
    return t


def del_missing_key(a):
    d = {1: a}
    del d[9]
    return 0


def del_through_alias(a):
    d = {1: a, 2: 5}
    e = d
    del e[1]
    return len(d)


def del_nondict_still_loud(a):
    # THE SYNTACTIC BOUNDARY: ingestion rewrites `del o[k]` for ANY receiver,
    # so the receiver's TYPE is decided in the evaluator's arm. CPython DELETES
    # here (list item deletion), which this tier does not have, so it refuses
    # rather than inventing an answer.
    xs = [a, 5]
    del xs[0]
    return len(xs)


def del_during_iteration(a):
    # SIZE changes -> CPython's RuntimeError, which the tier reproduces
    d = {1: a, 2: 5}
    t = 0
    for k in d:
        del d[k]
        t = t + k
    return t


def del_churn_then_break(a):
    # the ONE churn shape that is a MATCH, and for a reason that is not
    # "CPython was silent": the loop EXITS before the cursor re-reads, so the
    # guard is never reached.
    d = {1: a, 2: 5}
    t = 0
    for k in d:
        del d[2]
        d[3] = 6
        t = k
        break
    return t


def del_churn_first_key(a):
    # CPython completes SILENTLY here (measured); the tier refuses, because
    # the cursor re-reads and cannot know which layout it is in.
    d = {1: a, 2: 5, 3: 6}
    t = 0
    for k in d:
        if k == 1:
            del d[3]
            d[99] = 9
        t = t + k
    return t


def del_churn_same_key_back(a):
    # CPython completes SILENTLY (measured); same refusal, same reason.
    d = {1: a, 2: 5}
    t = 0
    for k in d:
        if k == 1:
            del d[2]
            d[2] = 9
        t = t + k
    return t


def del_churn_middle_key(a):
    # CPython RAISES its SECOND RuntimeError here (measured) -- a different
    # message from the size one. The tier refuses rather than reproduce a
    # message it cannot know it should emit.
    d = {1: a, 2: 5, 3: 6}
    t = 0
    for k in d:
        if k == 2:
            del d[1]
            d[99] = 9
        t = t + k
    return t
