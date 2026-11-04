"""leanpy corpus: A TOP-LEVEL CALL WITH AN OBSERVABLE EFFECT.

CPython prints "side effect" then "done". Two pipelines ago `x = talk()`
was a plain bind, so module initialization FOLDED it, the fold delegated
to the interpreter, the in-function `print` was out of tier, the attempt
failed, and `initFoldLive` ROLLED IT BACK — leanpy answered "done" alone,
a wrong answer rather than a refusal; `initNothingSkipped` then refused
the program, and THE ONE PIPELINE removed the fold that made the hole.

The last thing standing between this file and CPython's output was
`print` inside a function body, live since 2026-08-13. It now runs.
"""


def talk():
    print("side effect")
    return 1


x = talk()

print("done")
