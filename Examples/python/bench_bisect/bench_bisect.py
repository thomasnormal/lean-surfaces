"""CPython bisect_left/bisect_right, vendored verbatim for the Lean
verification benchmark (flagship Band A target).

Provenance:
  package : CPython standard library, module `bisect`
  version : Python 3.9.25 (system interpreter of this repo's toolchain)
  file    : /usr/lib64/python3.9/bisect.py, sha256
            6f213241b0d2c5cb8886c5615c6cc88f3a4ff200d7345b87a8f5bfa9d468a71b
  license : PSF License Agreement for Python 3.9.25 (PSF-2.0);
            Copyright (c) 2001-2026 Python Software Foundation.

Vendoring rules (python benchmark, Examples/python/bench_bisect):
  * bisect_right and bisect_left are BYTE-VERBATIM copies of bisect.py
    3.9.25 lines 15-35 and 50-70 (sha256 of the two segments:
    800f693a1fab81dc0beda51726778af89d1e4c3b544f8abbf577c7bd900a31f0
    ad01a97b7dce7a945d973cb6f7d4c11570e8c1b76f6dc7ba2fafda34c629d8e5). Do NOT edit their bodies.
  * insort_right/insort_left (list.insert mutation) and the module-level
    `bisect = bisect_right` aliases are NOT vendored; the C override block
    (`from _bisect import *`) is NOT vendored -- this file IS the pure
    Python reference implementation those lines would replace.
  * Python 3.9 signature `(a, x, lo=0, hi=None)`: NO keyword-only `key`
    parameter (that was added in 3.10) -- both functions here take four
    positional parameters, the last two with constant defaults.

Authenticity (2026-07-29, Python 3.9.25): bisect_left([1,2,2,3], 2) = 1,
bisect_right([1,2,2,3], 2) = 3, bisect_left([10,20,30], 25, 0, 3) = 2,
bisect_left([], 5) = 0 computed against this file AND against the
installed `bisect` module (C accelerated) -- both agree.
"""

def bisect_right(a, x, lo=0, hi=None):
    """Return the index where to insert item x in list a, assuming a is sorted.

    The return value i is such that all e in a[:i] have e <= x, and all e in
    a[i:] have e > x.  So if x already appears in the list, a.insert(x) will
    insert just after the rightmost x already there.

    Optional args lo (default 0) and hi (default len(a)) bound the
    slice of a to be searched.
    """

    if lo < 0:
        raise ValueError('lo must be non-negative')
    if hi is None:
        hi = len(a)
    while lo < hi:
        mid = (lo+hi)//2
        # Use __lt__ to match the logic in list.sort() and in heapq
        if x < a[mid]: hi = mid
        else: lo = mid+1
    return lo

def bisect_left(a, x, lo=0, hi=None):
    """Return the index where to insert item x in list a, assuming a is sorted.

    The return value i is such that all e in a[:i] have e < x, and all e in
    a[i:] have e >= x.  So if x already appears in the list, a.insert(x) will
    insert just before the leftmost x already there.

    Optional args lo (default 0) and hi (default len(a)) bound the
    slice of a to be searched.
    """

    if lo < 0:
        raise ValueError('lo must be non-negative')
    if hi is None:
        hi = len(a)
    while lo < hi:
        mid = (lo+hi)//2
        # Use __lt__ to match the logic in list.sort() and in heapq
        if a[mid] < x: lo = mid+1
        else: hi = mid
    return lo
