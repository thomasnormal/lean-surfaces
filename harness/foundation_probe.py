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
