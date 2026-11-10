"""A linear version of fib's first descent, for recursion boundary testing."""


def fib_left(n):
    if n < 2:
        return n
    return fib_left(n - 1)


def depth_compare(n):
    if n:
        return depth_compare(n - 1)
    return 1 < 2
