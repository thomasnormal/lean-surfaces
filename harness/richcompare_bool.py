"""Rows that cross CPython's RichCompareBool equality and key probes."""

def scalar_pair():
    return (True == 1, 1 == True, True == 2, 1 == 2)


def list_contains():
    xs = [True, 2]
    return (1 in xs, 2 in xs, 3 in xs)


def dict_key_probe():
    d = {True: 7, 2: 9}
    return (d[1], d.get(True, 0), 2 in d, 3 in d)


def nested_equality():
    return [[True, 2] == [1, 2], (True, 2) == (1, 2)]
