"""leanpy corpus: LIVE TOP-LEVEL CODE REBINDS A GLOBAL A FUNCTION READS —
a payoff row of THE ONE PIPELINE (docs/memory-model.md §the one pipeline).

`z = z + 41` makes `z` a module global in CPython, so `readz()` answers 42
the second time. Under the old prefix/suffix split the fold owned `z` and
the live run bound it in the script's LOCALS, invisible to function
frames, so the model would have answered a stale 1 — `suffixConsistent`
refused the whole file rather than say it. One pipeline, one store: the
top-level frame's locals ARE the module globals, so the call reads what
the statement wrote.
"""

z = 1


def readz():
    return z


print(readz())
z = z + 41
print(readz())
