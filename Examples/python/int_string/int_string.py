def parse_decimal(text):
    return int(text)


def grouped_offset(offset):
    return int("1_024") + offset


def signed_adjustment(offset):
    return offset + int(" \v\f-2_048\r\n")


def explicit_base(text, base):
    return int(text, base)


def keyword_base(text, base):
    return int(text, base=base)


def hex_offset(offset):
    return int("0x_fF", base=0) + offset


def missing_string(base):
    return int(base=base)


def duplicate_base(text, base):
    return int(text, base, base=base)


def too_many(text, base):
    return int(text, base, 0)


def total_before_keyword():
    return int("ff", base=16, other=0)


def too_many_keywords():
    return int(base=16, other=0, extra=0)


def unknown_keyword(base_first):
    if base_first:
        return int(base=16, other=0)
    return int(other=0, base=16)


def positional_string_only():
    return int(x="12", base=10)


def record(log, tag, value):
    log.append(tag)
    return value


def argument_effects():
    log = []
    value = int(record(log, 1, "ff"), base=record(log, 2, 16))
    return value, log


def arity_effects():
    log = []
    try:
        int(record(log, 1, "ff"), base=record(log, 2, 16), other=record(log, 3, 0))
    except TypeError:
        return log
    return []


def conversion_effects():
    log = []
    try:
        int(record(log, 1, "ff"), base=record(log, 2, 1))
    except ValueError:
        return log
    return []


def keyword_value_error():
    return int("ff", base=1 // 0)


def arity_value_error():
    return int("ff", 16, 1 // 0)


def long_invalid():
    return int(
        "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"
        "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"
        "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"
        "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"
        "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"
    )


def long_escaped_invalid():
    return int(
        "\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"
        "\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"
        "\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"
        "\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"
    )
