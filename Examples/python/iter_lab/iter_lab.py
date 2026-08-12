"""The H5 iteration-tier acceptance set: membership on every in-tier
container (str SUBSTRINGS, value tuples, boundary lists, namedtuples,
and the pre-existing dict/heap-list scans), `for` over a str, and the
`ord`/`chr` code-point pair -- every function here runs differentially
against CPython 3.9 (harness/cases.json). The loud frontier (a
surrogate `chr`, a heap-object operand) is pinned by whitelisted rows;
the faithful `TypeError`s (a non-str left operand of `in <string>`, a
non-iterable right operand, a mis-sized `ord`) are ordinary matching
rows -- the harness compares exception classes.
"""

from collections import namedtuple

Pt = namedtuple("Pt", "x y")


def in_str(s, sub):
    return sub in s


def not_in_str(s, sub):
    return sub not in s


def piece_test(q):
    # gen_moves' hot membership test (sunfish.py, Position.gen_moves)
    return q in " \nPNBRQK"


def promo_test(p):
    return p not in "PNBRQK"


def in_tuple(x):
    return x in (10, 20, 30)


def not_in_tuple(x):
    return x not in (10, 20, 30)


def in_list(xs, x):
    return x in xs


def in_ntuple(x):
    return x in Pt(3, 4)


def count_char(s, c):
    n = 0
    for ch in s:
        if ch == c:
            n += 1
    return n


def take_until(s, stop):
    # `for` over a str with an early `break`
    out = ""
    for ch in s:
        if ch == stop:
            break
        out = out + ch
    return out


def sum_ords(s):
    total = 0
    for ch in s:
        total += ord(ch)
    return total


def ord_of(s):
    return ord(s)


def chr_of(n):
    return chr(n)


def roundtrip(n):
    return ord(chr(n))


def shift(s, k):
    # ord/chr as a pair, over a `for`-iterated str
    out = ""
    for ch in s:
        out = out + chr(ord(ch) + k)
    return out


def in_str_bad_left(s, x):
    # CPython: "'in <string>' requires string as left operand, not int"
    return x in s


def in_int(x):
    # a non-iterable right operand: the faithful TypeError
    return x in 5


def chr_surrogate():
    # loud: CPython builds a lone-surrogate str, which Lean's Char (and
    # so every string in this model) cannot represent
    return chr(0xD800)


def chr_out_of_range(n):
    return chr(n)


def enum_sum(s):
    # `enumerate` in a module with NO generator def: it allocates a
    # generator FRAME, which `moduleGenFree` used to claim impossible —
    # the arm refused ordinary Python as an interpreter bug (2026-08-13)
    tot = 0
    for i, c in enumerate(s):
        tot += i * ord(c)
    return tot


def enum_first(s):
    # the frame is LAZY: `break` on the first step leaves the rest unread
    for i, c in enumerate(s):
        return i * 1000 + ord(c)
    return -1
