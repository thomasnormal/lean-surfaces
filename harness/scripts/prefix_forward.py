"""leanpy corpus: the FORWARD REFERENCE FROM THE G1 PREFIX — the second
hole the ordered admission closes.

`x = f()` is a plain bind, so it belongs to the G1-faithful prefix that
module initialization folds (and, when the fold refuses, executes) rather
than to the live suffix. The old rule only compared definition positions
against LIVE statements, so this file was admitted and the model happily
called `f` — CPython raises `NameError` and exits 1. `defsBoundBefore`
checks every top-level statement, prefix included, so the model now
refuses loudly instead of answering `1`.
"""
x = f()


def f():
    return 1


print(x)
