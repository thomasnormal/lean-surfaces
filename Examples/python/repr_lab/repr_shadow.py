def repr(value):
    return value + 11


def direct(value):
    return repr(value)


def captured_generator():
    return tuple(repr(value) for value in (1, 2))
