"""The admitted single-clause dictionary-comprehension surface."""


def from_range(n, probe):
    values = {i: i * i for i in range(n)}
    return (len(values), values.get(probe, -1))


def duplicate_keys(n):
    values = {i % 2: i for i in range(n)}
    return (values[0], values[1])


def bad_pair():
    return len(dict(x for x in [1]))


def bad_length():
    return len(dict((x,) for x in [1]))


def unhashable_key():
    return len({[1, 2]: 3 for _ in [0]})
