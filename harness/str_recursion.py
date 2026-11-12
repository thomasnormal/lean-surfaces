"""Recursion-limit probes for str()'s C entry and arity boundary."""

def valid(n):
    def leaf():
        try:
            str(1)
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
        try:
            str(1, 2)
            return 42
        except TypeError:
            return 27
    try:
        if n:
            return invalid(n - 1)
        return leaf()
    except RecursionError:
        return 11
