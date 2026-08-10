"""seq_lab — pass 3's value tiers at FUNCTION level (checks-only).

Tuple/namedtuple slices, tuple repetition, sum(it[, start]), tuple(it),
and range as an immediate value (materialize-per-use). The loud frontier
is pinned by refusal probes: range ==/indexing/membership/unpacking/
boundary, list slices, str repetition.
"""

from collections import namedtuple

Move = namedtuple("Move", "i j prom")


def slice_tuple(a, b):
    t = (10, 20, 30, 40, 50, 60, 70, 80)
    return t[a:b]


def slice_computed(i):
    # the padding loop's shape: computed bounds into an 8-wide row
    t = (10, 20, 30, 40, 50, 60, 70, 80)
    return t[i * 2 : i * 2 + 2]


def slice_step(k):
    t = (1, 2, 3, 4, 5, 6)
    return (t[::k], t[4:1:-1], t[-3:])


def slice_move(i):
    # a namedtuple slice is a PLAIN tuple (the class does not survive)
    m = Move(i, i + 7, "q")
    return m[0:2]


def repeat(n):
    return (0,) * n + (7,) * 2


def repeat_left(n):
    return n * (1, 2)


def repeat_bool():
    return (1, 2) * True


def sum_ints(n):
    return sum((1, 2, 3, n))


def sum_start(n):
    return sum([1, 2], n)


def sum_tuples():
    # the padding loop's fold: tuple concatenation from an empty start
    return sum(((1,), (2, 3)), ())


def sum_gen(n):
    return sum(i * i for i in range(n))


def sum_str_start():
    return sum([1], "x")


def sum_str_elems():
    return sum("ab")


def sum_arity():
    return sum(1, 2, 3)


def tuple_of_str(s):
    return tuple(s)


def tuple_of_list(n):
    xs = [1, 2, n]
    xs.append(4)
    return tuple(xs)


def tuple_of_gen(n):
    return tuple(2 * i for i in range(n))


def tuple_of_range(n):
    return tuple(range(n, 0, -1))


def tuple_of_int():
    return tuple(7)


def range_len(a, b, s):
    return len(range(a, b, s))


def range_for(n):
    acc = 0
    for i in range(n):
        acc = acc + i * i
    return acc


def range_reiter(n):
    # a range is RE-ITERABLE (it is not an iterator): both loops see the
    # full sequence — materialize-per-use is what makes this exact
    r = range(n)
    a = 0
    for i in r:
        a = a + i
    b = 0
    for i in r:
        b = b + i
    return (a, b)


def range_truthy(n):
    if range(n):
        return 1
    return 0


def range_zero_step():
    return range(1, 5, 0)


def range_next():
    return next(range(3))


def range_extremum(n):
    return (max(range(n)), min(range(n)))


def range_empty_max():
    return max(range(0))


def enum_range(n):
    acc = 0
    for i, v in enumerate(range(3, 3 + n)):
        acc = acc + i * v
    return acc


def range_eq(n):
    return range(n) == range(n)


def range_index(n):
    return range(n)[0]


def range_in(n):
    return 2 in range(n)


def range_boundary(n):
    return range(n)


def range_unpack():
    a, b = range(2)
    return a


def list_slice_loud(n):
    return [1, 2, 3][0:n]


def str_repeat_loud(n):
    return "ab" * n
