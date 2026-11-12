"""Rows for immediate and heap-backed iterator worker boundaries."""

def range_sum():
    total = 0
    for value in range(4):
        total += value
    return total


def tuple_sum():
    total = 0
    for value in (1, 2, 3):
        total += value
    return total


def live_list_growth():
    xs = [1]
    for value in xs:
        if value == 1:
            xs.append(2)
    return len(xs)
