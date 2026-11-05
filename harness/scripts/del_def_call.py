"""Deleting a module definition must remain visible to later function calls."""


def h():
    return 1


def g():
    return h()


del h
print(g())
