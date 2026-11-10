"""Recursion and ordering probes for sum()."""

def valid(n):
    def leaf():
        value = 7
        try:
            try:
                sum((1, 2))
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


def start(n):
    def leaf():
        value = 7
        try:
            try:
                sum((1, 2), 3)
                return 42
            except TypeError:
                return 20 + value
        except NameError:
            return 30 + value
    try:
        if n:
            return start(n - 1)
        return leaf()
    except RecursionError:
        return 11


def bad_type(n):
    def leaf():
        value = 7
        try:
            try:
                sum(3)
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
                sum()
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
                sum((1,), 2, 3)
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
                sum(iterable=(1,))
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
                sum(missing_name)
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
                sum((value := (1, 2)))
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
