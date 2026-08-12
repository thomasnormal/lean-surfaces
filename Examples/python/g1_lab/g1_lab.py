"""G1 boundary regressions (H1-proper hardening, found by leanpy v0):

* `read_m`: `M` is bound AFTER a top-level `while` — the G1 fold cannot
  know what the loop did, so the binding is POISONED (a stale value would
  be silently wrong); reads are loudly unsupported.
* `try_print`: `print` inside a function body. Loud until 2026-08-13
  ("the effect cannot thread the interpreter yet"); `print` is now an
  ordinary builtin appending to `World.stdout`, so the call returns `x`
  like CPython's. NOTE the boundary: `callFunction` returns a value and
  DROPS the world, so this row compares the return value only — stdout is
  observable through `CallsIn` and through leanpy's script surface, which
  is where `harness/scripts/fnprint.py` pins it."""


def read_m():
    return M


def try_print(x):
    print(x)
    return x


x = 1
while x < 3:
    x = x + 1
M = x
