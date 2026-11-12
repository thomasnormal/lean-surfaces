"""Rows for hash gating, bool/int collisions, and tuple key equality."""

def bool_int_collision():
    d = {True: 7, 2: 9}
    return (d[1], d.get(1, 0), len(d))


def tuple_collision():
    d = {(1, 2): 7}
    return d[(True, 2)]


def unhashable_probe():
    d = {1: 2}
    try:
        return d[[1]]
    except TypeError:
        return 17
