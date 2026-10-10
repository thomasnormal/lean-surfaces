from collections import namedtuple

Point = namedtuple("Point", "x y")
EmptyTuple = namedtuple("EmptyTuple", "")


class Plain:
    pass


class Custom:
    def __bool__(self):
        return False


def zero():
    return bool()


def of(value):
    return bool(value)


def containers():
    return (bool([]), bool([0]), bool({}), bool({0: 0}), bool(set([0])),
            bool(range(0)), bool(range(1)), bool(Point(0, 0)),
            bool(EmptyTuple()))


def instance():
    return bool(Plain())


def closure():
    def inner():
        return 0
    return bool(inner)


def one():
    yield 0


def generator():
    values = one()
    before = bool(values)
    drained = tuple(values)
    after = bool(values)
    return before, drained, after


def mutation():
    values = []
    result = bool(values.append(1))
    return result, bool(values), len(values)


def arity_two():
    return bool(0, 1)


def arity_three():
    return bool(0, 1, 2)


def shadow(value):
    def bool(item):
        return item + 2
    return bool(value)


def kwargs():
    return bool(value=1)


def first_class():
    constructor = bool
    return constructor(1)


def custom():
    return bool(Custom())
