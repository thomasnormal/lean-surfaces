from collections import namedtuple


Pair = namedtuple("Pair", "left right")


class Plain:
    pass


def repr_field(value):
    return f"[{value!r}]"


def str_field(value):
    return f"[{value!s}]"


def bare_field(value):
    return f"[{value}]"


def mixed(value):
    return f"{value!s}|{value!r}"


def debug(value):
    return f"{value=}"


def empty_spec(value):
    return f"{value!r:}"


def empty_bare_spec(value):
    return f"{value:}"


def effects():
    values = []
    rendered = f"{values.append(1)!r}:{values!r}:{values.append(2)!r}:{values!r}"
    return rendered, values


def argument_error():
    values = []
    try:
        f"{values.append(1)!r}:{1 // 0!r}:{values.append(2)!r}"
    except ZeroDivisionError:
        return values


def cyclic():
    values = []
    values.append(values)
    return f"{values!r}"


def named():
    return f"{Pair('x', [1, 2])!r}"


def local_shadow(value):
    def str(argument):
        raise ValueError

    def repr(argument):
        raise TypeError

    return f"{value}/{value!s}/{value!r}/{value=}"


def parameter_shadow(repr, str):
    return f"{True!r}:{False!s}"


def captured_generator():
    def str(argument):
        return argument + 10

    def repr(argument):
        return argument + 20

    return tuple(f"{value!r}:{value!s}" for value in (1, 2))


def instance():
    return f"{Plain()!r}"
