"""leanpy corpus: the forward reference from a direct top-level assignment.

`x = f()` is evaluated at its source position.  CPython and leanpy both
raise the faithful `NameError` before the later definition is bound; the
script executor checks this direct expression/assignment at runtime.
"""
x = f()


def f():
    return 1


print(x)
