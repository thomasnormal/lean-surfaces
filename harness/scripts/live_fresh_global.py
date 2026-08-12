"""leanpy corpus: LIVE TOP-LEVEL CODE BINDS A FRESH GLOBAL A FUNCTION
READS — the second payoff row of THE ONE PIPELINE.

`w = 7` creates a module global after `readw` is defined but before it is
called, so CPython answers 7. Under the prefix/suffix split the name was
absent from an always-analysable static table, so a call would have raised
a FAKE `NameError`, and `suffixConsistent` refused the file to avoid it.
Now the name is statically absent by construction and the absent arm
consults the live globals: it resolves exactly once the statement binding
it has run — and a call made BEFORE that still raises the genuine
`NameError` (`call_before_def.py` is the ordering row).
"""


def readw():
    return w


print(1)
w = 7
print(readw())
