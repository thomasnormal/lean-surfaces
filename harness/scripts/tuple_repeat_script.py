from collections import namedtuple

Pair = namedtuple("Pair", "x y")


def repeated(values, count):
    return values * count


def augmented(values, count):
    values *= count
    return values


def shallow_alias():
    value = {"v": 1}
    result = (value,) * 2
    value["v"] = 9
    return result[0]["v"]


values = (7, 8)
values *= 3
print(values)
print(3 * (1, 2))
print(repeated((7, 8), 0))
print(repeated((7, 8), -3))
print(repeated((7, 8), True))
print(False * (7, 8))
print(augmented((7, 8), 2))
print(() * 3)
print(() * -3)
print(Pair(7, 8) * 2)
print(2 * Pair(7, 8))
print(augmented(Pair(7, 8), 2))
print(len((7, 8) * 3))
print(shallow_alias())
