"""Foundation step 0 probes for the five CPython-protocol findings."""


def nan_contains(value):
    return value in [value]


def nan_list_equal(value):
    return [value] == [value]


def int_pow_negative(base, exponent):
    return base ** (-exponent)


def list_insert_huge(index):
    values = [1, 2]
    values.insert(index, 0)
    return values


def list_pop_huge(index):
    values = [1]
    return values.pop(index)


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
