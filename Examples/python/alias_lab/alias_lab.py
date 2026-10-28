"""Module-level def aliasing (docs/memory-model.md, the narrow slice).

Every function here runs differentially against CPython 3.9
(harness/cases.json); the aliases themselves are called BY NAME in the
rows, so the alias entry's dispatch is oracled, not assumed.
"""


def scale(x, k=2):
    return x * k


def gen_pair(n):
    yield n
    yield n + 1


scale2 = scale
double = scale2
chain1 = chain2 = scale
pair2 = gen_pair


def use_alias(x):
    return scale2(x)


def use_kw(x):
    return scale2(x, k=3)


def use_gen_alias(n):
    return list(pair2(n))


def read_alias():
    return scale2


def dead_alias():
    f = scale2
    return 0


def sorted_alias(values):
    f = sorted
    return f(values)


def max_alias(values):
    f = max
    return f(values)


def min_alias(values):
    f = min
    return f(values)


def abs_alias(value):
    f = abs
    return f(value)


def int_alias(value):
    f = int
    return f(value)


def float_alias(value):
    f = float
    return f(value)


def all_alias(values):
    f = all
    return f(values)


def any_alias(values):
    f = any
    return f(values)


def str_alias(value):
    f = str
    return f(value)


def sum_alias(values, start=0):
    f = sum
    return f(values, start)


def tuple_alias(value):
    f = tuple
    return f(value)


def list_alias(value):
    f = list
    return f(value)


def ord_alias(value):
    f = ord
    return f(value)


def chr_alias(value):
    f = chr
    return f(value)


def pow_alias(base, exponent):
    f = pow
    return f(base, exponent)


def round_alias(value):
    f = round
    return f(value)


def ascii_alias(value):
    f = ascii
    return f(value)


def hex_alias(value):
    f = hex
    return f(value)


def oct_alias(value):
    f = oct
    return f(value)


def bin_alias(value):
    f = bin
    return f(value)


def format_alias(value):
    f = format
    return f(value)


def range_alias(value):
    f = range
    return f(value)
