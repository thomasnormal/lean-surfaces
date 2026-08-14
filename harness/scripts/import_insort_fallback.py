"""Pass 0 (docs/memory-model.md paragraph "Import forms (Pass 0)"),
the 2.5 rows, insort half: bisect.py's pure `insort_right` behind the
guarded accelerator, results-only observation (the list is printed once
at the end). CPython runs the C `insort`; the model runs the pure def --
whose `a.insert(lo, x)` is OUTSIDE the tier today (`attrCallPlan` knows
append/pop only), so the HONEST registered verdict is "unsupported":
the model refuses loudly rather than diverging. The 2.5 obligation for
insort therefore stands OPEN (recorded in docs/backlog.md); when
`list.insert` lands, flip this row's expect to "match" -- that flip IS
the discharge. REBUILD-WINDOW."""


def insort_right(a, x, lo=0, hi=None):
    if hi is None:
        hi = len(a)
    while lo < hi:
        mid = (lo + hi) // 2
        if x < a[mid]:
            hi = mid
        else:
            lo = mid + 1
    a.insert(lo, x)


try:
    from _bisect import *
except ImportError:
    pass

a = [1, 3, 5]
insort_right(a, 4)
insort_right(a, 0)
insort_right(a, 6)
print(a)
