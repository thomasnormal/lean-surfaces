"""A function body cannot reach a definition CPython has not bound yet."""


def g():
    return h()


print(g())


def h():
    return 2
