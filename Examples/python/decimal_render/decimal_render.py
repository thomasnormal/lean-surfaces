from collections import namedtuple

Pair = namedtuple("Pair", "x y")


def scalar_str(value):
    return str(value)


def format_s(value):
    return "%s" % (value,)


def format_r(value):
    return "%r" % (value,)


def format_d(value):
    return "%d" % (value,)


def tuple_str(value):
    return str((value,))


def list_str(value):
    return str([value])


def dict_key_str(value):
    return str({value: 7})


def dict_value_str(value):
    return str({"value": value})


def range_stop_str(value):
    return str(range(value))


def range_start_str(value):
    return str(range(value, value))


def range_step_str(value):
    return str(range(0, 2, value))


def namedtuple_str(value):
    return str(Pair(value, 7))


def fstring_str(value):
    return f"{value}"


def sized_value(digits, sign):
    return sign * (10 ** digits - 1)


def scalar_length(digits, sign):
    return len(scalar_str(sized_value(digits, sign)))


def format_s_length(digits, sign):
    return len(format_s(sized_value(digits, sign)))


def format_r_length(digits, sign):
    return len(format_r(sized_value(digits, sign)))


def format_d_length(digits, sign):
    return len(format_d(sized_value(digits, sign)))


def tuple_length(digits, sign):
    return len(tuple_str(sized_value(digits, sign)))


def list_length(digits, sign):
    return len(list_str(sized_value(digits, sign)))


def dict_key_length(digits, sign):
    return len(dict_key_str(sized_value(digits, sign)))


def dict_value_length(digits, sign):
    return len(dict_value_str(sized_value(digits, sign)))


def range_stop_length(digits, sign):
    return len(range_stop_str(sized_value(digits, sign)))


def range_start_length(digits, sign):
    return len(range_start_str(sized_value(digits, sign)))


def range_step_length(digits, sign):
    return len(range_step_str(sized_value(digits, sign)))


def namedtuple_length(digits, sign):
    return len(namedtuple_str(sized_value(digits, sign)))


def fstring_length(digits, sign):
    return len(fstring_str(sized_value(digits, sign)))
