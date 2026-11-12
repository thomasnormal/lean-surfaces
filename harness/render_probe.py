"""Rows for scalar and heap-aware rendering worker overlap."""

def scalar_str():
    return (str(1), str(True), str(None))


def tuple_repr():
    return repr((1, 2))


def list_repr():
    return repr([1, 2])
