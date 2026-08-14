"""The bisect.py shape verbatim: pure defs, a guarded star import of a
missing accelerator, module-level aliases, alias calls."""


def find_spot(a, x):
    lo = 0
    hi = len(a)
    while lo < hi:
        mid = (lo + hi) // 2
        if x < a[mid]:
            hi = mid
        else:
            lo = mid + 1
    return lo


try:
    from _zzz_not_a_module import *
except ImportError:
    pass

locate = find_spot

print(locate([1, 3, 5, 7], 4))
print(locate([], 9))
print(find_spot([2, 4], 3) == locate([2, 4], 3))
