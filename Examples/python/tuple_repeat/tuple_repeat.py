from collections import namedtuple

Pair = namedtuple("Pair", "x y")


def repeat_right(values, count):
    return values * count


def repeat_left(count, values):
    return count * values


def repeat_aug(values, count):
    values *= count
    return values


def repeat_empty(count):
    return () * count


def repeat_right_length(count):
    result = (7, 8) * count
    return len(result)


def repeat_left_length(count):
    result = count * (7, 8)
    return len(result)


def repeat_aug_length(count):
    result = (7, 8)
    result *= count
    return len(result)


def repeat_empty_length(count):
    result = () * count
    return len(result)


def repeat_namedtuple(count):
    return Pair(7, 8) * count


def repeat_namedtuple_left(count):
    return count * Pair(7, 8)


def repeat_namedtuple_aug(count):
    result = Pair(7, 8)
    result *= count
    return result


def repeat_shallow_alias(count):
    value = {"v": 1}
    result = (value,) * count
    value["v"] = 9
    return result[0]["v"]
