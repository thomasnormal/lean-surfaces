"""leanpy corpus: MODULE INIT MUST NOT SILENTLY SKIP A STATEMENT.

`x = talk()` is a plain bind, so module initialization folds it; the fold
delegates to the interpreter, the in-function `print` is out of tier, the
attempt fails, and `initFoldLive` ROLLS IT BACK and poisons `x`. For the
closed FUNCTION surface that is right — nothing was observed, and a later
read of `x` refuses. For a whole PROGRAM it is not: CPython prints
"side effect" here, and leanpy used to answer "done" alone. Now the run
refuses loudly (`initNothingSkipped`, docs/memory-model.md §module-init
execution). `harness/scripts/init_raise_script.py` is the same hole with
an exception instead of output.
"""


def talk():
    print("side effect")
    return 1


x = talk()

print("done")
