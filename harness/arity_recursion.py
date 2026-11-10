def required(a, b):
    return a


def defaulted(a, b=2):
    return a


def generator(a, b):
    yield a


def plain_missing(n):
    if n:
        return plain_missing(n - 1)
    return required()


def plain_partial(n):
    if n:
        return plain_partial(n - 1)
    return defaulted()


def plain_extra(n):
    if n:
        return plain_extra(n - 1)
    return required(1, 2, 3)


def keyword_missing(n):
    if n:
        return keyword_missing(n - 1)
    return required(a=1)


def keyword_invalid(n):
    if n:
        return keyword_invalid(n - 1)
    return required(unknown=1)


def generator_missing(n):
    if n:
        return generator_missing(n - 1)
    generator()
    return 7


def closure_missing(n):
    def required(a, b):
        return a
    if n:
        return closure_missing(n - 1)
    return required()


def closure_extra(n):
    def required(a, b):
        return a
    if n:
        return closure_extra(n - 1)
    return required(1, 2, 3)


def none_params():
    return 7


def keyword_duplicate(n):
    if n:
        return keyword_duplicate(n - 1)
    return required(1, a=2)


def keyword_empty(n):
    if n:
        return keyword_empty(n - 1)
    return none_params(unknown=1)


def extra_with_unknown(n):
    if n:
        return extra_with_unknown(n - 1)
    return required(1, 2, 3, unknown=1)


def extra_with_duplicate(n):
    if n:
        return extra_with_duplicate(n - 1)
    return required(1, 2, 3, a=4)


def generator_valid_kw(n):
    if n:
        return generator_valid_kw(n - 1)
    generator(a=1, b=2)
    return 7


def duplicate_before_unknown(n):
    if n:
        return duplicate_before_unknown(n - 1)
    return required(1, a=2, unknown=3)


def unknown_before_duplicate(n):
    if n:
        return unknown_before_duplicate(n - 1)
    return required(1, unknown=3, a=2)
