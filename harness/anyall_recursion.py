"""Recursion and ordering probes for all() and any()."""

def all_values(n):
    def leaf():
        value = 7
        try:
            try:
                all((1, 2))
                return 42
            except TypeError:
                return 20 + value
        except NameError:
            return 30 + value
    try:
        if n:
            return all_values(n - 1)
        return leaf()
    except RecursionError:
        return 11


def any_values(n):
    def leaf():
        value = 7
        try:
            try:
                any((0, 1))
                return 42
            except TypeError:
                return 20 + value
        except NameError:
            return 30 + value
    try:
        if n:
            return any_values(n - 1)
        return leaf()
    except RecursionError:
        return 11


def all_invalid(n):
    def leaf():
        value = 7
        try:
            try:
                all(3)
                return 42
            except TypeError:
                return 20 + value
        except NameError:
            return 30 + value
    try:
        if n:
            return all_invalid(n - 1)
        return leaf()
    except RecursionError:
        return 11


def any_invalid(n):
    def leaf():
        value = 7
        try:
            try:
                any(3)
                return 42
            except TypeError:
                return 20 + value
        except NameError:
            return 30 + value
    try:
        if n:
            return any_invalid(n - 1)
        return leaf()
    except RecursionError:
        return 11


def all_missing(n):
    def leaf():
        value = 7
        try:
            try:
                all()
                return 42
            except TypeError:
                return 20 + value
        except NameError:
            return 30 + value
    try:
        if n:
            return all_missing(n - 1)
        return leaf()
    except RecursionError:
        return 11


def any_extra(n):
    def leaf():
        value = 7
        try:
            try:
                any(1, 2)
                return 42
            except TypeError:
                return 20 + value
        except NameError:
            return 30 + value
    try:
        if n:
            return any_extra(n - 1)
        return leaf()
    except RecursionError:
        return 11


def all_kw(n):
    def leaf():
        value = 7
        try:
            try:
                all(iterable=())
                return 42
            except TypeError:
                return 20 + value
        except NameError:
            return 30 + value
    try:
        if n:
            return all_kw(n - 1)
        return leaf()
    except RecursionError:
        return 11


def any_kw(n):
    def leaf():
        value = 7
        try:
            try:
                any(iterable=())
                return 42
            except TypeError:
                return 20 + value
        except NameError:
            return 30 + value
    try:
        if n:
            return any_kw(n - 1)
        return leaf()
    except RecursionError:
        return 11


def all_arg_error(n):
    def leaf():
        value = 7
        try:
            try:
                all(missing_name)
                return 42
            except TypeError:
                return 20 + value
        except NameError:
            return 30 + value
    try:
        if n:
            return all_arg_error(n - 1)
        return leaf()
    except RecursionError:
        return 11


def any_arg_effect(n):
    def leaf():
        value = 7
        try:
            try:
                any((value := (0, 1)))
                return 42
            except TypeError:
                return 20 + value
        except NameError:
            return 30 + value
    try:
        if n:
            return any_arg_effect(n - 1)
        return leaf()
    except RecursionError:
        return 11


def gen_all(n):
    def values():
        yield 0
        yield 1
    def leaf():
        g = values()
        try:
            all(g)
        except RecursionError:
            return 11
        return next(g, 9)
    try:
        if n:
            return gen_all(n - 1)
        return leaf()
    except RecursionError:
        return 12


def gen_any(n):
    def values():
        yield 0
        yield 1
    def leaf():
        g = values()
        try:
            any(g)
        except RecursionError:
            return 11
        return next(g, 9)
    try:
        if n:
            return gen_any(n - 1)
        return leaf()
    except RecursionError:
        return 12



def gen_recovery_all(n):
    def values():
        yield 0
        yield 1
    g = values()
    def descend(k):
        try:
            if k:
                return descend(k - 1)
            all(g)
            return 2
        except RecursionError:
            return 1
    result = descend(n)
    return result, next(g, 9)


def gen_recovery_any(n):
    def values():
        yield 0
        yield 1
    g = values()
    def descend(k):
        try:
            if k:
                return descend(k - 1)
            any(g)
            return 2
        except RecursionError:
            return 1
    result = descend(n)
    return result, next(g, 9)


def arg_effect_before_limit(n):
    def leaf():
        value = 7
        try:
            all((value := (0, 1)))
        except RecursionError:
            return value[1]
        return 9
    if n:
        return arg_effect_before_limit(n - 1)
    return leaf()
