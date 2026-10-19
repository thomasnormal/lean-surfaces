"""A recognized namedtuple class shadows a builtin exception name."""

from collections import namedtuple

ValueError = namedtuple("ValueError", "x")
StopIteration = namedtuple("StopIteration", "x")
Record = namedtuple("Record", "x")


def raise_value_error():
    raise ValueError


def raise_stop_iteration():
    raise StopIteration


def raise_record():
    raise Record


def catch_shadow(value):
    try:
        raise ValueError
    except TypeError:
        return value


def stop_generator():
    yield 1
    raise StopIteration


def generator_closed():
    g = stop_generator()
    first = next(g)
    try:
        next(g)
    except TypeError:
        return first * 10 + next(g, 7)


def generator_escape():
    return list(stop_generator())


def invalid_handler():
    try:
        return 1 // 0
    except ValueError:
        return 2


def handler_success(value):
    try:
        return value
    except ValueError:
        return 2


def handler_retained_state():
    seen = [0]
    try:
        try:
            seen.append(1)
            raise TypeError
        except ValueError:
            seen.append(2)
    except TypeError:
        seen.append(3)
    return seen
