"""The H4 generator acceptance set: generator functions as suspended
frames, `for`-loop consumption, abandonment by `break`/`return` leaving
the generator SUSPENDED, resumption by a second consumer, `next` with
and without a default, and generator EXPRESSIONS (lowered at ingestion
to generator functions, exactly as CPython compiles them).

Laziness is pinned the only way that cannot be faked: `first_over_inf`
and `any_over` consume INFINITE generators and terminate -- an eager
pre-expansion would diverge. That is the property sunfish's beta cutoff
depends on, and the reason a generator-free rewrite is not an option.

Every function here runs differentially against CPython 3.9
(harness/cases.json); the loud frontier (a yield in expression position,
`send`/`throw`, a generator crossing the call boundary) is pinned by
whitelisted rows.
"""

from itertools import count


def upto(n):
    i = 0
    while i < n:
        yield i
        i += 1


def naturals():
    i = 0
    while True:
        yield i
        i += 1


def upto_ret(n):
    # `return` inside a generator is EXHAUSTION, not a value
    i = 0
    while True:
        if i >= n:
            return
        yield i
        i += 1


def evens(n):
    # a generator consuming a generator, with `continue` inside the loop
    for i in upto(n):
        if i % 2 == 1:
            continue
        yield i


def nested(n):
    for x in evens(n):
        yield x + 100


def total(n):
    s = 0
    for x in upto(n):
        s += x
    return s


def total_ret(n):
    s = 0
    for x in upto_ret(n):
        s += x
    return s


def sum_nested(n):
    s = 0
    for x in nested(n):
        s += x
    return s


def first_over(n, k):
    for x in upto(n):
        if x > k:
            return x
    return -1


def first_over_inf(k):
    # terminates ONLY because the generator is lazy
    for x in naturals():
        if x > k:
            return x
    return -1


def two_phase(n):
    # the SAME generator consumed by two loops: the second resumes where
    # the first abandoned it -- `break` leaves the frame SUSPENDED
    g = upto(n)
    a = -1
    for x in g:
        a = x
        break
    b = -1
    for y in g:
        b = y
        break
    return a * 100 + b


def drain_then_more(n):
    g = upto(n)
    s = 0
    for x in g:
        s += x
    # exhausted: the second loop runs zero times
    for y in g:
        s += 1000
    return s


def next_of(n):
    g = upto(n)
    return next(g)


def next_twice(n):
    g = upto(n)
    a = next(g)
    b = next(g)
    return a * 100 + b


def next_default(n):
    g = upto(n)
    return next(g, -1)


def next_exhausted(n):
    g = upto(n)
    for x in g:
        pass
    return next(g, -7)


def next_stops(n):
    # no default: the faithful StopIteration
    g = upto(n)
    return next(g)


def aliased(n):
    # two names, ONE generator object: advancing through either advances
    # the other (a generator is heap identity, never a value)
    g = upto(n)
    h = g
    a = next(g)
    b = next(h)
    return a * 100 + b


def squares_upto(n):
    # a generator EXPRESSION, lowered to a generator function
    return next((x * x for x in upto(n)), -1)


def first_big(n, k):
    return next((x for x in upto(n) if x > k), -1)


def any_over(k):
    # a genexp over an INFINITE generator, consumed by `next`
    return next((x for x in naturals() if x > k), -1)


def genexp_sum(n):
    s = 0
    for y in (x + 1 for x in upto(n)):
        s += y
    return s


def next_of_int(n):
    return next(n)


def gen_at_boundary(n):
    return upto(n)


def _sender(n):
    # a yield in EXPRESSION position: the `send` channel, deliberately
    # out of tier -- creating the generator is fine, STEPPING it is loud
    x = yield n
    return


def send_is_loud(n):
    return next(_sender(n), -1)


def enum_str(s):
    out = 0
    for i, c in enumerate(s):
        out += i * ord(c)
    return out


def enum_start(s, k):
    first = -1
    for i, c in enumerate(s, k):
        first = i
        break
    return first


def enum_list(xs):
    t = 0
    for i, v in enumerate(xs):
        t += i * v
    return t


def enum_lazy(s, stop):
    # laziness through `enumerate`: stops without walking the tail
    n = 0
    for i, c in enumerate(s):
        n += 1
        if c == stop:
            break
    return n


def count_ray(start, step, k):
    # sunfish's ray shape: an INFINITE count, ended by `break`
    last = -1
    for j in count(start, step):
        if j > k:
            break
        last = j
    return last


def count_default():
    for j in count():
        if j > 3:
            return j
    return -1


def enum_of_int(n):
    return next(enumerate(n), -1)


def bad(n):
    # a builtin exception firing INSIDE a step: the second resume divides
    # by n (the docs/memory-model.md paragraph "exceptions" obligation --
    # pin the status-after-exn behaviour BEFORE the exception tier builds
    # on the stepper)
    yield 1
    yield 1 // n
    yield 3


def bad_first(n):
    # the exception is NOT raised at creation, nor by the first step
    return next(bad(n))


def bad_second(n):
    # the second step raises out of the resume (n = 0), and the whole
    # call propagates CPython's ZeroDivisionError
    g = bad(n)
    next(g)
    return next(g)


def drain_assigned(n):
    # pass 4 (docs/memory-model.md "bound() end-to-end"): a body-ASSIGNED
    # local captured by an IMMEDIATELY-DRAINED genexp -- the correction's
    # `all(... >= val_lower ...)` shape
    lim = n - 2
    if all(x < lim for x in range(n)):
        return 1
    return sum(1 for x in range(n) if x >= lim)


def drain_assigned_param(n):
    # a PARAMETER the body rebinds, captured under an immediate drain --
    # bound()'s `depth = max(depth, 0)` then `all(depth > 1 ...)`
    n = n + 1
    return sum(x * n for x in range(3))


def gen_assigned_lazy(n):
    # NOT directly drained (the genexp binds to a name first): the
    # by-value snapshot could go stale before consumption -- REFUSED
    lim = n
    g = (x < lim for x in range(n))
    return all(g)


def drain_unbound(n):
    # no direct-child binding BEFORE the genexp line (the assign hides
    # inside an if) -- boundness is unprovable, REFUSED (CPython would
    # answer 0 for n = 0 but NameError for n > 0)
    if n > 100:
        late = 1
    return sum(late for x in range(n))


# pass 5 (docs/memory-model.md "yield from"): statement-position
# `yield from <genexp>` is INLINED at ingestion -- gen_moves's
# promotion arm. The drivers consume in-module (generators never cross
# the boundary).

def yf_promote(i, j):
    # the gen_moves shape: genexp over a str literal, elt reading
    # enclosing locals
    yield from ((i, j, prom) for prom in "NBRQ")


def yf_promote_drive(i, j):
    out = ""
    for t in yf_promote(i, j):
        out = out + t[2]
    return out


def yf_live(n):
    # the inlined loop reads the ENCLOSING frame live: `i` is a loop
    # variable of the enclosing generator, rebound between delegations
    for i in range(n):
        yield from ((i, k) for k in range(2))


def yf_live_drive(n):
    s = 0
    for t in yf_live(n):
        s = 10 * s + t[0] + t[1]
    return s


def yf_filter(n):
    # filters ride the same guardWith lowering as every genexp
    yield from (x * x for x in range(n) if x % 2 == 0)
    yield -1


def yf_filter_drive(n):
    s = 0
    for v in yf_filter(n):
        s += v
    return s


def yf_list(n):
    # REFUSED: the iterable is not a genexp (delegation to a list)
    yield from [1, 2, n]


def yf_list_drive(n):
    return sum(yf_list(n))


def yf_leak(n):
    # REFUSED: the genexp target `x` occurs elsewhere in the body --
    # inlining would leak the binding into the enclosing frame
    x = n
    yield from (x for x in range(n))
    yield x


def yf_leak_drive(n):
    return sum(yf_leak(n))


def walrus_filter(k):
    # pass 7 (docs/memory-model.md §the walrus filter): the shipped QS
    # ordering-line shape -- the filter binds (v := ...), the element
    # reads it, filter-before-sort skips sorting the sub-threshold tail
    out = 0
    for val, m in sorted(((v, m) for m in (1, 2, 3, 4, 5) if (v := m * m) >= k), reverse=True):
        out = out * 100 + val + m
    return out


def walrus_leak(k):
    # REFUSED: the walrus name is read OUTSIDE the genexp -- PEP 572
    # leaks the binding into this frame, so the frame-local lowering
    # would be observably wrong; the genexp stays un-lowered (loud)
    t = sum((v for m in (1, 2, 3) if (v := m) >= k), 0)
    return t + v


def walrus_stmt(n):
    # REFUSED: a walrus outside a genexp filter stays the generic
    # unsupported expression (loud, never half-structured)
    if (v := n + 1) > 2:
        return v
    return 0
