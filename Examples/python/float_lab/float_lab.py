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


def addition():
    return 1.0 + 2.0


def nonfinite_division_still_loud():
    return 1e999 / 2.0


def infinite_quotient():
    return float("inf") / -2.0


def infinite_denominator():
    return 5.0 / float("-inf")


def infinite_augmented():
    value = -0.0
    value /= float("-inf")
    return value


def infinite_zero_caught():
    try:
        return float("inf") / -0.0
    except ZeroDivisionError:
        return 19


def division_nonfinite_overflow(mode, value=1e999):
    if mode == 0:
        return 10 ** 400 / value
    return value / 10 ** 400


def indeterminate_division_still_loud():
    return float("inf") / float("-inf")


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


def count_prefix(start, step):
    values = count(start, step)
    return next(values), next(values), next(values)


def count_many():
    return count(1, 2, 3)


def add(left, right):
    return left + right


def subtract(left, right):
    return left - right


def multiply(left, right):
    return left * right


def augmented():
    value = 0.5
    value += 0.25
    value -= 0.125
    value *= -2.0
    return value


def mixed_rounding():
    return 9007199254740993 + 1.0


def cancel(value):
    return value - value


def arithmetic_conversion_error(operation):
    if operation == 0:
        return 10 ** 400 + 0.0
    if operation == 1:
        return 0.0 - 10 ** 400
    return 10 ** 400 * 0.0


def nan_arithmetic_still_loud(operation):
    if operation == 0:
        return 1e999 + -1e999
    if operation == 1:
        return 1e999 - 1e999
    return 0.0 * 1e999


def constructor(value):
    return float(value)


def constructor_zero():
    return float()


def constructor_tenth():
    return float("0.1")


def constructor_unicode():
    return float("\u3000٠.١\u3000")


def constructor_rounding():
    return float(9007199254740993)


def constructor_overflow():
    return float(10 ** 400)


def constructor_many():
    return float(1, 2)


def constructor_bad_then_many():
    return float("bad", 1)


def constructor_order():
    return float(1, 1 // 0)


def constructor_invalid_caught():
    try:
        return float("1._0")
    except ValueError:
        return 17


def constructor_shadow():
    def float(value):
        return value + 1
    return float(7)


def constructor_keyword():
    return float(x=1)


def constructor_heap():
    return float([])


def constructor_comprehension():
    return [float(value) for value in ("0.1", "1.5")]


def floor_pair(left, right):
    return left // right, left % right, divmod(left, right)


def floor_tenth():
    return 1.0 // 0.1


def remainder_tenth():
    return 1.0 % 0.1


def floor_infinite():
    return 5.0 // float("-inf")


def remainder_infinite():
    return 5.0 % float("-inf")


def floor_augmented():
    value = 1.0
    value //= 0.1
    value %= 4.0
    return value


def floor_zero(mode):
    if mode == 0:
        return 1.0 // -0.0
    if mode == 1:
        return 1.0 % -0.0
    return divmod(1.0, -0.0)


def floor_zero_caught(mode):
    try:
        if mode == 0:
            return 1.0 // -0.0
        if mode == 1:
            return 1.0 % -0.0
        return divmod(1.0, -0.0)
    except ArithmeticError:
        return 23


def floor_conversion_order(mode, value=1e999):
    if mode == 0:
        return 10 ** 400 // value
    if mode == 1:
        return value % 10 ** 400
    return divmod(value, 10 ** 400)
