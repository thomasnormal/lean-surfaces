from collections import namedtuple


Pair = namedtuple("Pair", "left right")


class Plain:
    pass


def rejected_start(iterable, start):
    return sum(iterable, start)


def dict_start(start):
    return sum({1: 2}, start)


def set_start(start):
    return sum({1, 2}, start)


def list_start(start):
    return sum([1, 2], start)


def range_start(start):
    return sum(range(10 ** 100), start)


def element_evaluated(start):
    return sum([1 // 0], start)


def namedtuple_start(start):
    return sum(Pair(1, 2), start)


def function_start(start):
    function = lambda: 0
    return sum(function, start)


def instance_start(start):
    return sum(Plain(), start)


def values():
    yield 7
    yield 1 // 0


def generator_start(start):
    return sum(values(), start)


def generator_untouched(start):
    cursor = values()
    try:
        sum(cursor, start)
    except TypeError:
        return next(cursor)


def enumerate_untouched(start):
    cursor = enumerate([5])
    try:
        sum(cursor, start)
    except TypeError:
        return next(cursor)


def arguments_evaluated(start):
    effects = []

    def iterable():
        effects.append(1)
        return 0

    def initial():
        effects.append(2)
        return start

    try:
        sum(iterable(), initial())
    except TypeError:
        return tuple(effects)
