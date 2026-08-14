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

