"""A later scalar alias shadow must be visible inside a function body."""


def f():
    return 1


a = f


def g():
    return a()


a = 3
print(g())
