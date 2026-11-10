"""Foundation step 0 probes for the five CPython-protocol findings."""


def nan_contains(value):
    return value in [value]


def nan_list_equal(value):
    return [value] == [value]


def nan_tuple_order(value):
    return (value,) < (value,)


def nan_sorted(value):
    return sorted([value, 1.0])


def nan_max(value):
    return max([value, 1.0])


def nan_dict_key(value):
    values = {value: 1}
    return values[value]


def int_pow_negative(base, exponent):
    return base ** (-exponent)


def float_pow_conversion(base):
    return base ** 1.0


def list_insert_huge(index):
    values = [1, 2]
    values.insert(index, 0)
    return values


def list_insert_boundary(index):
    values = [1, 2]
    values.insert(index, 0)
    return values


def list_pop_huge(index):
    values = [1]
    return values.pop(index)


def list_pop_boundary(index):
    values = [1, 2]
    return values.pop(index)


def list_pop_empty_huge(index):
    values = []
    return values.pop(index)


def list_subscript_huge(index):
    return [1][index]


def tuple_subscript_huge(index):
    return (1,)[index]


def string_subscript_huge(index):
    return "a"[index]


def bytes_subscript_huge(index):
    return b"a"[index]


def range_subscript_huge(index):
    return range(1)[index]


def list_slice_huge(index):
    return [1][index:]


def string_slice_huge(index):
    return "a"[:index]


def range_len_huge():
    return len(range(2 ** 64))


def bisect_fallback_negative_hi():
    values = [1, 2, 3]
    lo = 0
    hi = -1
    while lo < hi:
        mid = (lo + hi) // 2
        if values[mid] < 5:
            lo = mid + 1
        else:
            hi = mid
    return lo


def deep_linear(n):
    if n <= 0:
        return 0
    return deep_linear(n - 1) + 1


def gen_capture_unpack():
    p = 3
    g = (p for _ in (1,))
    p, *rest = (9, 8)
    return list(g)


def gen_capture_walrus():
    p = 3
    g = (p for _ in (1,))
    (p := 7)
    return list(g)


def gen_capture_del():
    p = 3
    g = (p for _ in (1,))
    del p
    return list(g)


def gen_iter_deferred(value):
    g = (x for x in value)
    return 1


def negative_pow_exponent_overflow(base):
    return base ** -(1 << 1100)


def negative_pow_exponent_boundary(shift):
    return 0 ** -(1 << shift)


def negative_pow_base_overflow(exponent):
    return (1 << 1100) ** -exponent


def float_pow_base_overflow():
    return (1 << 1100) ** 1.0


def float_pow_exponent_overflow():
    return 0.0 ** -(1 << 1100)


def mixed_div_left_overflow():
    return (1 << 1100) / 0.0


def mixed_div_right_overflow():
    return 1.0 / (1 << 1100)


def integer_div_huge_ratio():
    return (1 << 1100) / (1 << 1100)
