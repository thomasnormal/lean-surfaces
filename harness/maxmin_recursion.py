"""Recursion and argument-order probes for max() and min()."""


def max_valid(n):
    def leaf():
        value = 7
        try:
            try:
                max((1, 2))
                return 42
            except TypeError:
                return 20 + value
        except NameError:
            return 30 + value
    try:
        if n:
            return max_valid(n - 1)
        return leaf()
    except RecursionError:
        return 11


def min_valid(n):
    def leaf():
        value = 7
        try:
            try:
                min((1, 2))
                return 42
            except TypeError:
                return 20 + value
        except NameError:
            return 30 + value
    try:
        if n:
            return min_valid(n - 1)
        return leaf()
    except RecursionError:
        return 11


def max_two(n):
    def leaf():
        value = 7
        try:
            try:
                max(1, 2)
                return 42
            except TypeError:
                return 20 + value
        except NameError:
            return 30 + value
    try:
        if n:
            return max_two(n - 1)
        return leaf()
    except RecursionError:
        return 11


def min_two(n):
    def leaf():
        value = 7
        try:
            try:
                min(1, 2)
                return 42
            except TypeError:
                return 20 + value
        except NameError:
            return 30 + value
    try:
        if n:
            return min_two(n - 1)
        return leaf()
    except RecursionError:
        return 11


def max_bad_type(n):
    def leaf():
        value = 7
        try:
            try:
                max(3)
                return 42
            except TypeError:
                return 20 + value
        except NameError:
            return 30 + value
    try:
        if n:
            return max_bad_type(n - 1)
        return leaf()
    except RecursionError:
        return 11


def min_bad_type(n):
    def leaf():
        value = 7
        try:
            try:
                min(3)
                return 42
            except TypeError:
                return 20 + value
        except NameError:
            return 30 + value
    try:
        if n:
            return min_bad_type(n - 1)
        return leaf()
    except RecursionError:
        return 11


def max_missing(n):
    def leaf():
        value = 7
        try:
            try:
                max()
                return 42
            except TypeError:
                return 20 + value
        except NameError:
            return 30 + value
    try:
        if n:
            return max_missing(n - 1)
        return leaf()
    except RecursionError:
        return 11


def min_missing(n):
    def leaf():
        value = 7
        try:
            try:
                min()
                return 42
            except TypeError:
                return 20 + value
        except NameError:
            return 30 + value
    try:
        if n:
            return min_missing(n - 1)
        return leaf()
    except RecursionError:
        return 11


def max_empty(n):
    def leaf():
        value = 7
        try:
            try:
                max(())
                return 42
            except ValueError:
                return 31 + value
        except NameError:
            return 30 + value
    try:
        if n:
            return max_empty(n - 1)
        return leaf()
    except RecursionError:
        return 11


def min_empty(n):
    def leaf():
        value = 7
        try:
            try:
                min(())
                return 42
            except ValueError:
                return 31 + value
        except NameError:
            return 30 + value
    try:
        if n:
            return min_empty(n - 1)
        return leaf()
    except RecursionError:
        return 11


def max_effect(n):
    def leaf():
        value = 7
        try:
            try:
                max((value := (1, 2)))
                return 42
            except TypeError:
                return 20 + value
        except NameError:
            return 30 + value
    try:
        if n:
            return max_effect(n - 1)
        return leaf()
    except RecursionError:
        return 11


def min_effect(n):
    def leaf():
        value = 7
        try:
            try:
                min((value := (1, 2)))
                return 42
            except TypeError:
                return 20 + value
        except NameError:
            return 30 + value
    try:
        if n:
            return min_effect(n - 1)
        return leaf()
    except RecursionError:
        return 11
