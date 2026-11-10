"""Definition-table position confirmation witness."""


def g():
    return h()


print(g())


def h():
    return 2


def f():
    return 1


def caller():
    return f()


print(caller())


def f():
    return 2


print(caller())
