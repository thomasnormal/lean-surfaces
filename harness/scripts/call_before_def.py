"""leanpy v0 corpus: a call site textually before the def.

CPython and leanpy both raise the faithful ``NameError`` at the call: the
script executor checks direct references at their source position even though
the ingested function table is position-independent."""
print(f())


def f():
    return 1
