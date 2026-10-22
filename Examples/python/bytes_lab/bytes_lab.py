def literal():
    return b"ab\x00\xff"


def length():
    return len(b"ab\x00\xff")


def indexing():
    value = b"ab\x00\xff"
    return value[0], value[-1], value[True]


def rendering():
    value = b"a\n\xff"
    return repr(value), str(value), f"{value!r}"


def concat_repeat():
    return b"ab" + b"c", b"ab" * 2, 2 * b"x"


def slicing():
    return b"abcdef"[1:5:2]


def equality_order():
    return b"a" == b"a", b"a" < b"b", b"a" != b"b"


def iterate():
    return tuple(b"ab")


def identity(value=b"ab\x00\xff"):
    return value


def render(value):
    return repr(value), str(value), ascii(value), f"{value!r}", "%r" % value, "%s" % value, f"{value}"


def index(value, position):
    return value[position]


def index_oob():
    return b"a"[3]


def slice_bytes(value, lower, upper, step):
    return value[lower:upper:step]


def repeat(value, count):
    return value * count


def contains(value, probe):
    return probe in value


def consumers(value):
    return tuple(value), list(value), sorted(value), sum(value), any(value), all(value)


def extrema(value):
    return min(value), max(value)


def unpack(value):
    left, right = value
    return left, right


def loop(value):
    total = 0
    for element in value:
        total += element
    return total


def comprehension(value):
    return [element + 1 for element in value]


def keys(value):
    table = {value: 3, b"ab": 4}
    return len(table), table[value], len(set(value))


def ordinal(value):
    return ord(value)


def tuple_keys(value):
    table = {(value,): 7}
    return table[(value,)]


def sum_start():
    return sum([], b"")


def sum_start_noniterable():
    return sum(1, b"")


def sum_values():
    yield 1 // 0


def sum_start_lazy():
    return sum(sum_values(), b"")


def enumerate_bytes(value):
    return tuple(enumerate(value, 3))


def numeric_int_still_loud():
    return int(b"\xff")


def numeric_int():
    return int(b" +1_2\n"), int(b"-0"), int(b"0007")


def numeric_int_invalid():
    return int(b"12x")


def numeric_float_still_loud():
    return float(b"1.5")


def iterator_still_loud():
    return next(iter(b"ab"))


def formatting_still_loud():
    return b"%s" % b"a"


def dict_still_loud():
    return len(dict(b""))
