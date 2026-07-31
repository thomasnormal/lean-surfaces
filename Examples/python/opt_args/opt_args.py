# Examples/python/opt_args/opt_args.py — tier-feature exercise for
# F1 (literal parameter defaults) and F2 (`is None` / `is not None`).
# Differential rows in harness/cases.json call every function below with
# CPython and the Lean interpreter side by side; the harness passes int
# arguments only, so None/str/bool values flow through defaults and
# intra-module calls (both in-tier).
#
# Def-time-vs-call-time note (asserted here, verified by the rows): all
# defaults below are LITERALS (int/bool/str/None), so CPython's evaluate-
# defaults-once-at-def-time semantics is observationally identical to the
# interpreter's fill-at-call-time — a literal's value cannot be mutated,
# rebound, or depend on evaluation order. The mutable-default footgun
# (`def f(x=[])`) is non-literal and stays args_unsupported.


def clamp(x, lo=0, hi=None):
    if hi is None:
        hi = 100
    if x < lo:
        return lo
    if x > hi:
        return hi
    return x


def pad(n, fill=0, flag=False, sep=""):
    if flag:
        n = n + fill
    return (n, sep)


def is_none(v):
    return v is None


def not_none(v):
    return v is not None


def probe(x):
    if x == 0:
        return is_none(None)
    return is_none(x)


def probe_not(x):
    if x == 0:
        return not_none(None)
    return not_none(x)


def latest(a, b=None):
    if b is not None and a < b:
        return b
    return a


def none_is_none():
    return None is None
