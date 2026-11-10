"""Recursion and ordering probes for abs()."""

def valid(n):
    def leaf():
        value = 7
        try:
            try:
                abs(-3)
                return 42
            except TypeError:
                return 20 + value
        except NameError:
            return 30 + value
    try:
        if n:
            return valid(n - 1)
        return leaf()
    except RecursionError:
        return 11


def bad_type(n):
    def leaf():
        value = 7
        try:
            try:
                abs('bad')
                return 42
            except TypeError:
                return 20 + value
        except NameError:
            return 30 + value
    try:
        if n:
            return bad_type(n - 1)
        return leaf()
    except RecursionError:
        return 11


def missing(n):
    def leaf():
        value = 7
        try:
            try:
                abs()
                return 42
            except TypeError:
                return 20 + value
        except NameError:
            return 30 + value
    try:
        if n:
            return missing(n - 1)
        return leaf()
    except RecursionError:
        return 11


def extra(n):
    def leaf():
        value = 7
        try:
            try:
                abs(1, 2)
                return 42
            except TypeError:
                return 20 + value
        except NameError:
            return 30 + value
    try:
        if n:
            return extra(n - 1)
        return leaf()
    except RecursionError:
        return 11


def keyword(n):
    def leaf():
        value = 7
        try:
            try:
                abs(x=3)
                return 42
            except TypeError:
                return 20 + value
        except NameError:
            return 30 + value
    try:
        if n:
            return keyword(n - 1)
        return leaf()
    except RecursionError:
        return 11


def arg_error(n):
    def leaf():
        value = 7
        try:
            try:
                abs(missing_name)
                return 42
            except TypeError:
                return 20 + value
        except NameError:
            return 30 + value
    try:
        if n:
            return arg_error(n - 1)
        return leaf()
    except RecursionError:
        return 11


def effect(n):
    def leaf():
        value = 7
        try:
            try:
                abs((value := 3))
                return 42
            except TypeError:
                return 20 + value
        except NameError:
            return 30 + value
    try:
        if n:
            return effect(n - 1)
        return leaf()
    except RecursionError:
        return 11



def effect_before_limit(n):
    def leaf():
        value = 7
        try:
            try:
                abs((value := -3))
            except TypeError:
                return 20 + value
        except RecursionError:
            return 30 + value
        return 42
    if n:
        return effect_before_limit(n - 1)
    return leaf()


def keyword_effect_before_limit(n):
    def leaf():
        value = 7
        try:
            try:
                abs(x=(value := 3))
            except TypeError:
                return 20 + value
        except RecursionError:
            return 30 + value
        return 42
    if n:
        return keyword_effect_before_limit(n - 1)
    return leaf()
