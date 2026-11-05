"""Static function tables cannot model a module redefinition."""


def f():
    return 1


def g():
    return f()


print(g())


def f():
    return 2


print(g())
