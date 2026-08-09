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
