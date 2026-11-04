"""Rebind after alias: the alias is a static call entry and the later
ordinary assignment shadows it in the live module frame, so both CPython
and leanpy print 7."""


def f(x):
    return x + 1


g = f
g = 7
print(g)
