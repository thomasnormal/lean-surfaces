"""leanpy corpus: the increasing integer set rendering slice.

The renderer admits only the deterministic CPython 3.9 order for this
increasing integer shape; arbitrary hash-table orders remain loud.
"""

s = set([1, 2, 3])
print(len(s))
print(s)
