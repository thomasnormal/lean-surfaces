"""leanpy corpus: PRINTING CONTAINERS — CPython's two-level render rule.

`print` applies `str()` to its arguments and `repr()` to everything
INSIDE a container, which is why `print("a")` has no quotes and
`print(["a"])` does. Loud until 2026-08-13 ("repr subtleties"), which is
a fair description: the quote CPython picks, its escape set, the
one-element tuple's trailing comma, a namedtuple's `field=value` form and
the `[...]` a self-referential list prints are each a place to be subtly
wrong, so every line here is compared against the pinned CPython.

What stays LOUD is what cannot be rendered exactly: a set (hash order),
an instance/closure/generator (identity), and a non-ASCII string, whose
printability is a Unicode table this model never guesses
(`print_set.py`, `print_nonascii.py`).
"""

from collections import namedtuple

Move = namedtuple("Move", "i j prom")

print([1, 2, 3])
print([])
print(["a", "b"])
print((1,))
print(())
print((1, 2))
print({"a": 1, "b": [2, 3]})
print({})
print([None, True, False])
print(list(range(4)))
print(range(4))
print(range(0, 10, 2))
print("it's")
print(["it's", 'say "hi"', "q'\"both"])
print(["tab\there", "nl\nhere", "\\back", "del\x7f", "ctl\x01"])
print([[1, [2]], 3])
print(Move(1, 2, ""))
print([Move(1, 2, "x")])
print({Move(1, 2, ""): 5})
print([-1, 0, 10 ** 20])
print("a", [1], (2,), {"k": None})

xs = [1]
xs.append(xs)
print(xs)
