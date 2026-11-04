def floordiv(a, b):
    return a // b


def mod(a, b):
    return a % b


def powi(a, b):
    return a ** b


def builtin_powi(a, b):
    return pow(a, b)


def builtin_pow_mod(a, b, m):
    return pow(a, b, m)


def choose(a, b):
    return a or b


def chain(a, b, c):
    return a < b < c


def idx(i):
    return [10, 20, 30][i]
