def values():
    if 1 < 2:
        yield 1


def descend(n, it):
    if n:
        return descend(n - 1, it)
    return next(it)


def run(n):
    return descend(n, values())


def catch_then_next(n):
    it = values()
    try:
        descend(n, it)
    except RecursionError:
        return next(it, -1)
    return -2


def descend_for(n, it):
    if n:
        return descend_for(n - 1, it)
    for item in it:
        return item
    return -1


def run_for(n):
    return descend_for(n, values())


def run_enumerate(n):
    return descend(n, enumerate((7,)))


def descend_no_args(n):
    if n:
        return descend_no_args(n - 1)
    return next()


def run_closed(n):
    it = values()
    next(it)
    next(it, -1)
    return descend(n, it)


def run_closed_for(n):
    it = values()
    next(it)
    next(it, -1)
    return descend_for(n, it)
