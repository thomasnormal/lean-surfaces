"""kw_lab — call-site keyword arguments (H6): the acceptance battery.

Every function runs differentially against CPython (harness/cases.json)
and is pinned by #py_check lines in spec.lean: keyword merges onto module
functions (holes filled from literal defaults), keyword-value EVALUATION
ORDER (positionals first, then keyword values left to right — observed
through which exception fires), the faithful binding TypeErrors
(unexpected keyword / multiple values / missing required argument), a
namedtuple-subclass method called with keywords (the shipped file's
`pos.rotate(nullmove=True)` shape), a keyword call on a shadowed name
(the callable check comes AFTER argument evaluation), and the LOUD
refusals: namedtuple keyword CONSTRUCTION and builtin keywords.
"""
from collections import namedtuple

Pt = namedtuple("Pt", "x y")


class Vec(namedtuple("Vec", "x y")):
    def scaled(self, k=2, flip=False):
        return self.x * k + (-self.y if flip else self.y)


def base(a, b=2, c=3):
    return a * 100 + b * 10 + c


def two_req(a, b):
    return a - b


def tag(sep="+"):
    return "a" + sep + "b"


def kw_plain(a):
    # the hole at `b` fills from its literal default
    return base(a, c=9)


def kw_all(a):
    # every parameter by keyword, written out of parameter order
    return base(c=a, b=a, a=a)


def kw_swap(x):
    # binding is by NAME, not by keyword position
    return two_req(b=x, a=1)


def kw_order(a):
    # keyword VALUES evaluate left to right: b's ZeroDivisionError (a=0)
    # fires before c's NameError (a!=0)
    return base(a, b=1 // a, c=nope)


def kw_pos_order(a):
    # positionals evaluate before any keyword value
    return two_req(1 // a, b=nope)


def kw_unexpected(a):
    return base(a, d=1)


def kw_multiple(a):
    return base(a, a=1)


def kw_missing(x):
    return two_req(a=x)


def method_kw(a):
    # the shipped file's rotate(nullmove=True) shape: a keyword call on a
    # namedtuple-subclass method, `self` prepended before the merge
    return Vec(a, 3).scaled(flip=True)


def method_kw_default(a):
    return Vec(a, 3).scaled(k=5)


def tag_kw():
    return tag(sep="-")


def shadow_kw(base):
    # the callee NAME resolves to the parameter; the callable CHECK comes
    # after the arguments evaluate, exactly CPython's order
    return base(1, c=9)


def ntuple_kw(a):
    # namedtuple keyword CONSTRUCTION: loud (a wrong field-order guess
    # would be silent corruption) — CPython returns a*10+1 here
    return Pt(x=a, y=1).x * 10 + Pt(x=a, y=1).y


def builtin_kw():
    # builtins take no keywords in the tier: loud (CPython: TypeError)
    return len(obj=[1, 2])


def sorted_kw(a):
    # sorted(reverse=True): descending stable (the H6 draining tier)
    return sorted([3, 1, a], reverse=True)
