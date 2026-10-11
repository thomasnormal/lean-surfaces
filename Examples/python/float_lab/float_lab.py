from itertools import count


def tenth():
    return 1.0 / 10.0


def mixed_left():
    return 5 / 2.0


def mixed_right():
    return 5.0 / 2


def integer_true():
    return 5 / 2


def signed_zero():
    return 0 / -2


def comparisons():
    return 1.0 == 1, 1.5 == 1, 9007199254740992.0 < 9007199254740993


def truthiness():
    return bool(0.0), bool(-0.0), bool(1.0)


def zero_division():
    return 1.0 / 0.0


def conversion_overflow():
    return 10 ** 400 / 1.0


def divide(left, right):
    return left / right


def integer_ratio():
    return 10 ** 400 / 10 ** 400


def integer_overflow():
    return 10 ** 400 / 1


def conversion_before_zero():
    return 10 ** 400 / 0.0


def ordering(left, right):
    return left < right, left <= right, left > right, left >= right


def unary(value):
    return +value, -value, abs(value), int(value), bool(value)


def rendering(value):
    return repr(value), str(value), f"{value!r}", "%s|%r|%d" % (value, value, value)


def default(value=0.1):
    return value


def numeric_sequence():
    return sorted([1.5, -2.0, 1, 0.0]), max(1.5, 2, -1.0), min(1.5, 2, -1.0)


def arithmetic_error(mode):
    try:
        if mode == 0:
            return 1 / 0
        if mode == 1:
            return 1.0 / 0.0
        return 10 ** 400 / 0.0
    except ArithmeticError:
        return "caught"


def addition_still_loud():
    return 1.0 + 2.0


def nonfinite_division_still_loud():
    return 1e999 / 2.0


def keys_still_loud():
    return {1.0: "one"}


def nested_keys_still_loud():
    return {(1.0,): "one"}


def attribute_still_loud():
    return (1.0).is_integer()


def nan_equality_still_loud(value):
    return value == value


def nan_sort_still_loud(value):
    return sorted([2.0, value, 1.0])


def count_head(start, step):
    return next(count(start, step))


def count_many():
    return count(1, 2, 3)
