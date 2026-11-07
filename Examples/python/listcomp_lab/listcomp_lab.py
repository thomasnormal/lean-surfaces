"""Native one-generator list-comprehension differential rows."""


def squares(n):
    return [i * i for i in range(n)]


def filtered(xs):
    return [x * 2 for x in xs if x > 0]


def list(value):
    return "shadow"


def shadowed_global():
    return [x for x in (1, 2)]


def shadowed_local():
    list = 3
    return [x for x in (1, 2)]


def walrus_filter(n):
    return [x for x in range(n) if (seen := x) > 0]


def from_generator(n):
    return [x for x in (y for y in range(n))]
