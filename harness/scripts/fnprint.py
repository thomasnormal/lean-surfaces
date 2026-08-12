"""leanpy corpus: PRINT INSIDE A FUNCTION BODY — a payoff row.

Loud until 2026-08-13 ("the effect cannot thread the mutual block"), which
walled off essentially every real program: functions are where Python
prints. `print` is now an ordinary builtin inside the interpreter, so the
call prints and returns `None`, the chunk lands in `World.stdout`, and the
runner boundary maps it to a line — CPython's own output.
"""


def shout(x):
    print(x)


shout(3)
