def round_float(value):
    return round(value)

def round_float_ties():
    return round(0.5), round(1.5), round(2.5), round(-0.5), round(-1.5), round(-2.5)

def round_float_large():
    return round(1e300)

def round_float_nan():
    return round(float("nan"))

def round_float_infinity():
    return round(float("inf"))


def round_float_zero(value):
    return round(value, 0)


def round_int_zero(value):
    return round(value, 0)


def round_bool_zero(value):
    return round(value, False)


def round_int_positive(value):
    return round(value, 2)


def round_bool_positive(value):
    return round(value, True)


def round_float_one(value):
    return round(value, 1)


def round_float_two(value):
    return round(value, 2)
