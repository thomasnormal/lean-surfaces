"""Pass 0 (docs/memory-model.md paragraph "Import forms (Pass 0)"),
the 2.5 rows, insort half: bisect.py's pure `insort_right` behind the
guarded accelerator, results-only observation (the list is printed once
at the end). CPython runs the C `insort`; the model runs the pure def
through the `list.insert` tier (docs/memory-model.md paragraph
"list.insert"), and the registered MATCH -- pure fallback vs the C
accelerator, same list -- IS the discharge of the memo-2.5 insort
obligation (this row expected "unsupported" until the tier landed)."""


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
