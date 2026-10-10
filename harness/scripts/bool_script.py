from collections import namedtuple

Point = namedtuple("Point", "x y")
EmptyTuple = namedtuple("EmptyTuple", "")


class Plain:
    pass


def one():
    yield 0


def arg(value):
    print(value)
    return value


print(bool(), bool(None), bool(0), bool(-1), bool(False), bool(True))
print(bool(""), bool("0"), bool(()), bool((0,)), bool([]), bool([0]))
print(bool({}), bool({0: 0}), bool(set([0])), bool(range(0)), bool(range(1)))
print(bool(Point(0, 0)), bool(EmptyTuple()), bool(Plain()))
values = one()
print(bool(values))
print(tuple(values))
print(bool(values))
items = []
print(bool(items.append(1)), bool(items), len(items))
try:
    bool(arg(0), arg(1))
except TypeError:
    print("arity two")
try:
    bool(arg(0), arg(1), arg(2))
except TypeError:
    print("arity three")
