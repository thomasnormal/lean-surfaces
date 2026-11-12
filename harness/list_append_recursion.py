"""Recursion-limit probes for list.append()'s C entry and arity boundary."""

def valid(n):
    def leaf():
        xs = []
        try:
            xs.append(1)
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
        xs = []
        try:
            xs.append(1, 2)
            return 42
        except TypeError:
            return 27
    try:
        if n:
            return invalid(n - 1)
        return leaf()
    except RecursionError:
        return 11
