"""Starred unpacking targets (the tail of the starred-target design)."""

def tail(xs):
    a, *rest = xs
    return (a, rest)


def head(xs):
    *rest, z = xs
    return (rest, z)


def middle(xs):
    a, *rest, z = xs
    return (a, rest, z)


def empty_middle(xs):
    a, *rest, z = xs
    return (a, rest, z)


def from_string():
    a, *rest = "abc"
    return (a, rest)


def from_range():
    a, *rest = range(4)
    return (a, rest)


def too_short(xs):
    a, *rest, z = xs
    return (a, rest, z)


def noniterable():
    a, *rest = 5
    return (a, rest)
