from collections import namedtuple


Pair = namedtuple("Pair", "left right")


class Plain:
    pass


class Custom:
    def __repr__(self):
        return "custom"


def of(value):
    return repr(value)


def containers():
    return repr(([], [1, "x"], {"x": [None, True]}, (1,), ()))


def named():
    return repr(Pair("x", [1, 2]))


def ranges():
    return repr((range(True), range(False, 3, True), range(5, 0, -2)))


def recursive_list():
    values = []
    values.append(values)
    return repr(values)


def recursive_dict():
    values = {}
    values["self"] = values
    return repr(values)


def shared_path():
    values = [1]
    return repr((values, values))


def updated_argument():
    values = []
    return repr((values.append(1), values))


def no_arguments():
    return repr()


def two_arguments():
    return repr(1, 2)


def arity_effects():
    values = []
    try:
        repr(values.append(1), values.append(2), values.append(3))
    except TypeError:
        return values


def argument_failure():
    return repr(1 // 0)


def excess_argument_failure():
    return repr(1, 1 // 0)


def keyword():
    return repr(object=1)


def first_class():
    return repr


def alias_call(value):
    f = repr
    return f(value)


def instance():
    return repr(Plain())


def custom():
    return repr(Custom())


def set_value():
    return repr(set([1, 2]))


def closure():
    def inner():
        return 1
    return repr(inner)


def generator():
    return repr(value for value in (1, 2))


def local_shadow():
    def repr(value):
        return value + 7
    return repr(3)


def parameter_shadow(repr):
    return repr(1)


def generator_shadow():
    def repr(value):
        return value + 7
    return tuple(repr(value) for value in (1, 2))


def large_length(digits):
    return len(repr(10 ** (digits - 1)))


def deep(depth):
    value = 0
    for index in range(depth):
        value = [value]
    return repr(value)
