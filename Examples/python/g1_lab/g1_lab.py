"""G1 boundary regressions (H1-proper hardening, found by leanpy v0):

* `read_m`: `M` is bound AFTER a top-level `while` — the G1 fold cannot
  know what the loop did, so the binding is POISONED (a stale value would
  be silently wrong); reads are loudly unsupported.
* `try_print`: `print` inside a function body — the effect cannot thread
  the interpreter yet; a NameError here would be a WRONG exception
  (CPython prints), so the call is loudly unsupported instead."""


def read_m():
    return M


def try_print(x):
    print(x)
    return x


x = 1
while x < 3:
    x = x + 1
M = x
