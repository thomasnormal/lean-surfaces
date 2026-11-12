"""Recursion-limit probes for dict.get()'s C entry and arity boundary."""

def valid(n):
    def leaf():
        d = {1: 2}
        try:
            d.get(1, 0)
            return 42
        except TypeError:
            return 27
    try:
        if n:
            return valid(n - 1)
        return leaf()
    except RecursionError:
        return 11


def invalid(n):
    def leaf():
        d = {1: 2}
        try:
            d.get(1, 2, 3)
            return 42
        except TypeError:
            return 27
    try:
        if n:
            return invalid(n - 1)
        return leaf()
    except RecursionError:
        return 11
