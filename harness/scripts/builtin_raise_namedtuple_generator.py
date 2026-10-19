from collections import namedtuple

StopIteration = namedtuple("StopIteration", "x")


def g():
    yield 1
    raise StopIteration


gen = g()
print(next(gen))
try:
    next(gen)
except TypeError:
    print("not an exception class")
print(next(gen, 7))
