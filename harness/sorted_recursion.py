"""Probe sorted entry and list.sort recursion boundaries."""
def sorted_valid(n):
    def leaf():
        try:
            sorted((2, 1))
            return 42
        except TypeError:
            return 27
    try:
        if n:
            return sorted_valid(n - 1)
        return leaf()
    except RecursionError:
        return 11

def sorted_empty(n):
    def leaf():
        try:
            sorted(())
            return 42
        except TypeError:
            return 27
    try:
        if n:
            return sorted_empty(n - 1)
        return leaf()
    except RecursionError:
        return 11

def sorted_singleton(n):
    def leaf():
        try:
            sorted((1,))
            return 42
        except TypeError:
            return 27
    try:
        if n:
            return sorted_singleton(n - 1)
        return leaf()
    except RecursionError:
        return 11

def sorted_bad_type(n):
    def leaf():
        try:
            sorted(3)
            return 42
        except TypeError:
            return 27
    try:
        if n:
            return sorted_bad_type(n - 1)
        return leaf()
    except RecursionError:
        return 11

def sorted_missing(n):
    def leaf():
        try:
            sorted()
            return 42
        except TypeError:
            return 27
    try:
        if n:
            return sorted_missing(n - 1)
        return leaf()
    except RecursionError:
        return 11

def sorted_extra(n):
    def leaf():
        try:
            sorted((), ())
            return 42
        except TypeError:
            return 27
    try:
        if n:
            return sorted_extra(n - 1)
        return leaf()
    except RecursionError:
        return 11

def sorted_reverse(n):
    def leaf():
        try:
            sorted((2, 1), reverse=True)
            return 42
        except TypeError:
            return 27
    try:
        if n:
            return sorted_reverse(n - 1)
        return leaf()
    except RecursionError:
        return 11

def sorted_bad_kw(n):
    def leaf():
        try:
            sorted((), bogus=1)
            return 42
        except TypeError:
            return 27
    try:
        if n:
            return sorted_bad_kw(n - 1)
        return leaf()
    except RecursionError:
        return 11

def sorted_rev_bad_type(n):
    def leaf():
        try:
            sorted(3, reverse=True)
            return 42
        except TypeError:
            return 27
    try:
        if n:
            return sorted_rev_bad_type(n - 1)
        return leaf()
    except RecursionError:
        return 11


def sorted_effect(n):
    def leaf():
        try:
            sorted((int("3"),))
            return 42
        except TypeError:
            return 27
    try:
        if n:
            return sorted_effect(n - 1)
        return leaf()
    except RecursionError:
        return 11

def sorted_deep_generator(n):
    def descend(k):
        if k:
            return descend(k - 1)
        return 1
    def source(k):
        yield descend(k)
    try:
        sorted(source(n))
        return 42
    except RecursionError:
        return 11


def sorted_bad_keyword_noniterable():
    return sorted(3, bogus=1)


def sorted_generator_state(n):
    def descend(k):
        if k:
            return descend(k - 1)
        return 1
    def source(k):
        yield descend(k)
    g = source(n)
    caught = 0
    try:
        sorted(g)
    except RecursionError:
        caught = 1
    return caught, next(g, -1)
