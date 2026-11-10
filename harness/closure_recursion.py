"""CPython recursion entry and unwind for ordinary and generator closures."""


def direct(n):
    def descend(k):
        if k:
            return descend(k - 1)
        return 7
    return descend(n)


def frame(n):
    def leaf():
        return 7
    if n:
        return frame(n - 1)
    return leaf()


def unwind(n):
    try:
        return frame(n)
    except RecursionError:
        return 42


def normal_unwind(n):
    def leaf():
        return 7
    if n:
        return normal_unwind(n - 1)
    leaf()
    return leaf()


def catch_and_retry(n):
    def leaf():
        return 7
    try:
        if n:
            return catch_and_retry(n - 1)
        return leaf()
    except RecursionError:
        return leaf()


def generator_create(n):
    def values():
        yield 7
    if n:
        return generator_create(n - 1)
    values()
    return 7


def generator_resume(n):
    def values():
        yield 7
    if n:
        return generator_resume(n - 1)
    return next(values())


def exception_then_call(n):
    def fail():
        return 1 // 0
    def leaf():
        return 7
    if n:
        return exception_then_call(n - 1)
    try:
        fail()
    except ZeroDivisionError:
        return leaf()


def bad_arity(n):
    def leaf(value):
        return value
    if n:
        return bad_arity(n - 1)
    return leaf()


def raise_class_unwind(n):
    def fail():
        raise ValueError
    try:
        if n:
            return raise_class_unwind(n - 1)
        return fail()
    except ValueError:
        return 42
