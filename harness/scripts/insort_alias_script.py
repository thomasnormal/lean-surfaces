"""The alias tier composed with `list.insert` (docs/memory-model.md
paragraphs "module-level def aliasing" and "list.insert"): the bisect.py
consumer shape end to end -- pure `insort_right` defs, the module-level
`insort = insort_right` alias, calls THROUGH the alias mutating one
list in place, printed once at the end. CPython and the model must
agree byte for byte."""


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


insort = insort_right

a = [2, 4, 8]
insort(a, 6)
insort(a, 1)
insort(a, 16)
insort(a, 4)
print(a)
print(insort_right(a, 3))
