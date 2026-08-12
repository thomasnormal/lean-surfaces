"""leanpy corpus: A TOP-LEVEL CALL WITH AN OBSERVABLE EFFECT.

CPython prints "side effect" then "done". Two pipelines ago `x = talk()`
was a plain bind, so module initialization FOLDED it, the fold delegated
to the interpreter, the in-function `print` was out of tier, the attempt
failed, and `initFoldLive` ROLLED IT BACK — leanpy answered "done" alone,
a wrong answer rather than a refusal; `initNothingSkipped` then refused
the program.

With THE ONE PIPELINE the statement simply executes, and the refusal is
the honest one: `print` inside a function body is outside the tier
(`fnprint.py` is the same wall reached directly). No fold, no rollback,
nothing skipped — the row now pins that the blocker is a construct rather
than an architecture.
"""


def talk():
    print("side effect")
    return 1


x = talk()

print("done")
