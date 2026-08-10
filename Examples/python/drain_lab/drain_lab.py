"""drain_lab — the H6 draining consumers: the acceptance battery.

`sorted`/`max`/`min` DRAIN a generator to exhaustion; `any`/`all` stop at
the first deciding element and leave the generator SUSPENDED — the
partial drain is observable by iterating the remainder. General-order
`sorted` (one relation with `<`): tuples lexicographic and class-erased,
strs by code point, bools kept AS bools (`sorted([True, 0, 2])` keeps
the True object), `reverse=True` descending STABLE (never
sort-then-reverse). Mixed value kinds refuse loudly — expect-unsupported
rows, never guessed error classes.
"""
from itertools import count


def squares_mod(n, m):
    i = 0
    while i < n:
        yield (i * i) % m
        i = i + 1


def flags_except(n):
    # truthy at every index but n
    i = 0
    while i < 5:
        yield i != n
        i = i + 1


def only_at(n):
    # truthy exactly at index n
    i = 0
    while i < 5:
        yield i == n
        i = i + 1


def sorted_gen(n, m):
    return sorted(squares_mod(n, m))


def sorted_gen_rev(n, m):
    return sorted(squares_mod(n, m), reverse=True)


def sorted_tuples(a, b):
    return sorted([(a, "x"), (b, "a"), (a, "a")])


def sorted_tuples_rev(a, b):
    return sorted([(a, "x"), (b, "a"), (a, "a")], reverse=True)


def sorted_str(s):
    return sorted(s)


def sorted_str_rev(s):
    return sorted(s, reverse=True)


def sorted_bools():
    return sorted([1, True, 0, False, 2])


def sorted_bools_rev():
    # descending STABLE: equals keep first-encountered order — a reversal
    # would forge [..., False, 0, ...]
    return sorted([1, True, 0, False, 2], reverse=True)


def sorted_mixed(a):
    # int vs str: CPython raises TypeError; the tier refuses loudly
    return sorted([a, "s"])


def max_gen(n, m):
    return max(squares_mod(n, m))


def min_gen(n, m):
    return min(squares_mod(n, m))


def max_gen_empty():
    return max(squares_mod(0, 7))


def max_str(s):
    return max(s)


def max_tuples(a, b):
    return max((a, "x"), (b, "a"))


def all_stops(n):
    # all() SHORT-CIRCUITS at the first falsy yield; the generator stays
    # SUSPENDED — the remainder is still there to iterate
    g = flags_except(n)
    stopped = all(g)
    rest = 0
    for x in g:
        rest = rest + 1
    return (stopped, rest)


def any_stops(n):
    g = only_at(n)
    found = any(g)
    rest = 0
    for x in g:
        rest = rest + 1
    return (found, rest)


def any_infinite():
    # laziness is load-bearing: `count()` never exhausts; `any` stops at
    # the first truthy value (1)
    return any(count())


def all_of_str(s):
    # every 1-char str is truthy; only the empty string gives True
    # vacuously with no falsy chars — all() over "" is True
    return all(s)


def any_of_list(a, b):
    return any([a, b])


def all_of_tuple(a, b):
    return all((a, b))
