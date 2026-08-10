"""The H5 string-tier acceptance set: slices (both step directions,
omitted/negative/clamped bounds, CPython's step-first validation order)
and the method trio swapcase/isupper/index — every function here runs
differentially against CPython 3.9 (harness/cases.json). The loud
frontier (non-ASCII case mapping, out-of-tier str methods, list slices,
index start/end arguments) is pinned by whitelisted rows."""


def rev(s):
    return s[::-1]


def mid(s, a, b):
    return s[a:b]


def head(s, n):
    return s[:n]


def tail(s, n):
    return s[n:]


def every_second(s):
    return s[::2]


def back_step(s, a, b):
    return s[a:b:-2]


def copy_all(s):
    return s[:]


def swap(s):
    return s.swapcase()


def isup(s):
    return s.isupper()


def idx(s, t):
    return s.index(t)


def board_flip(s):
    # Position.rotate's exact string chain (sunfish.py line 231)
    return s[::-1].swapcase()


def put(board, i, p):
    # Position.move's put lambda, as a def (sunfish.py line 238)
    return board[:i] + p + board[i + 1 :]


def slice_of_int(n):
    return n[0:2]


def step_zero(s):
    return s[::0]


def bad_lower(s, t):
    return s[t:]


def order_probe(s, t):
    # the step validates FIRST (PySlice_Unpack): ValueError, not the
    # lower bound's TypeError
    return s[t::0]


def swap_arg_raises(s):
    return s.swapcase(1)


def idx_arg_raises(s, n):
    return s.index(n)


def upper_of(s):
    # LIVE since H6 (`value()`'s capture lookup needs it); non-ASCII
    # stays loud
    return s.upper()


def lower_flag(s):
    return s.islower()


def list_slice_is_loud():
    return [1, 2, 3][::-1]


def idx_start_is_loud(s, t, a):
    return s.index(t, a)
