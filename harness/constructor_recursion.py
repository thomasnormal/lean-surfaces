"""CPython recursion units around user-defined class construction."""


class Recursive:
    def __init__(self, n):
        if n > 0:
            Recursive(n - 1)


def construct_depth(n):
    Recursive(n)
    return n


class Raises:
    def __init__(self):
        raise ValueError


def catch_then_construct(n):
    try:
        Raises()
    except ValueError:
        return construct_depth(n)


class TruthRecursive:
    def __init__(self, n):
        if n:
            TruthRecursive(n - 1)


def truth_depth(n):
    TruthRecursive(n)
    return n


def catch_recursion_then_construct(n):
    try:
        Recursive(n)
    except RecursionError:
        return construct_depth(2)
    return n
