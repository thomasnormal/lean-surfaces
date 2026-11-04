"""Pass 0 (docs/memory-model.md paragraph "Import forms (Pass 0)"),
the 2.5 rows (docs/c-intrinsics-proposal.md, accelerator-fallback
equivalence): bisect.py's PURE index functions, its guarded-accelerator
structure inlined. Under CPython the `from _bisect import *` SUCCEEDS
and the C accelerator OVERRIDES the pure defs, so every printed result
below comes from the C module; under the model the import raises, the
guard catches it, and the pure defs run. A MATCH is therefore the 2.5
assertion itself for `bisect_left`/`bisect_right`: nothing observable
differs between the accelerator and the fallback on these rows. Any
divergence is a blocker, not a footnote. The `insort` half of the
obligation is import_insort_fallback.py (open: `list.insert` is outside
the tier today). REBUILD-WINDOW: measured when the shared rebuild
lands."""


def bisect_right(a, x, lo=0, hi=None):
    if hi is None:
        hi = len(a)
    while lo < hi:
        mid = (lo + hi) // 2
        if x < a[mid]:
            hi = mid
        else:
            lo = mid + 1
    return lo


def bisect_left(a, x, lo=0, hi=None):
    if hi is None:
        hi = len(a)
    while lo < hi:
        mid = (lo + hi) // 2
        if a[mid] < x:
            lo = mid + 1
        else:
            hi = mid
    return lo


try:
    from _bisect import *
except ImportError:
    pass

a = [1, 2, 4, 4, 8]
print(bisect_left(a, 4))       # first admissible slot among equals
print(bisect_right(a, 4))      # past the run of equals
print(bisect_left(a, 0))       # below the range: 0
print(bisect_right(a, 9))      # above the range: len(a)
print(bisect_left([], 3))      # empty sequence: 0
print(bisect_left(a, 4, 1, 3)) # explicit lo/hi window
print(bisect_right(a, 1, 0, 1))
