"""leanpy corpus: the `dict(…)` CONSTRUCTOR (2026-08-13).

`dict()` is the empty mapping, `dict(k=v, …)` builds one in the call's own
order (duplicate keywords are a SyntaxError, so no insert can collide),
and `dict(d)` is CPython's shallow COPY — a fresh object, never an alias,
which is the whole point of writing it.

This is the last construct standing between the SHIPPED sunfish.py and a
complete module initialization under leanpy: its `opt_ranges = dict(QS=(0,
300), …)` was the file's named blocker.
"""

d = dict(a=1, b=2)
print(d)
print(len(d), d["a"])

e = dict()
print(e, len(e))

f = dict(d)
print(f, f == d, f is d)
f["c"] = 3
print(len(d), len(f))

print(dict(x=(0, 300), y=[1], z=None))
