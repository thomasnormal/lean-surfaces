"""Recursion and argument-order probes for round()."""

def valid(n):
    def leaf():
        try:
            round(1.5)
            return 42
        except TypeError:
            return 27
    try:
        if n:
            return valid(n - 1)
        return leaf()
    except RecursionError:
        return 11

def ndigits(n):
    def leaf():
        try:
            round(1.25, 1)
            return 42
        except TypeError:
            return 27
    try:
        if n:
            return ndigits(n - 1)
        return leaf()
    except RecursionError:
        return 11

def int_valid(n):
    def leaf():
        try:
            round(7)
            return 42
        except TypeError:
            return 27
    try:
        if n:
            return int_valid(n - 1)
        return leaf()
    except RecursionError:
        return 11

def bad_type(n):
    def leaf():
        try:
            round("x")
            return 42
        except TypeError:
            return 27
    try:
        if n:
            return bad_type(n - 1)
        return leaf()
    except RecursionError:
        return 11

def missing(n):
    def leaf():
        try:
            round()
            return 42
        except TypeError:
            return 27
    try:
        if n:
            return missing(n - 1)
        return leaf()
    except RecursionError:
        return 11

def extra(n):
    def leaf():
        try:
            round(1.5, 1, 2)
            return 42
        except TypeError:
            return 27
    try:
        if n:
            return extra(n - 1)
        return leaf()
    except RecursionError:
        return 11

def keyword(n):
    def leaf():
        try:
            round(number=1.5)
            return 42
        except TypeError:
            return 27
    try:
        if n:
            return keyword(n - 1)
        return leaf()
    except RecursionError:
        return 11

def effect(n):
    def leaf():
        try:
            round(int("3"))
            return 42
        except TypeError:
            return 27
    try:
        if n:
            return effect(n - 1)
        return leaf()
    except RecursionError:
        return 11

def keyword_effect(n):
    def leaf():
        try:
            round(number=int("3"))
            return 42
        except TypeError:
            return 27
    try:
        if n:
            return keyword_effect(n - 1)
        return leaf()
    except RecursionError:
        return 11

