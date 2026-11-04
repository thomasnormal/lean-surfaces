def str(value):
    return value + 10


def repr(value):
    return value + 20


def fields(value):
    return f"{value}/{value!s}/{value!r}"


def captured():
    return tuple(f"{value!r}:{value!s}" for value in (1, 2))
