"""import_lab -- the Pass 0 import-forms acceptance set
(docs/memory-model.md paragraph "Import forms (Pass 0)").

REBUILD-WINDOW battery: registered WITH the implementation (the
star_lab discipline), runnable only when the shared rebuild lands the
Lean side. Every row here uses an INVENTORY-ABSENT module
(`zzz_no_such_module`), so CPython and the model take the SAME branch
and the differential is exact by construction:

* happy_fallback -- a guarded from-import of a missing module: the
  raise is caught, the handler runs, the module completes (MATCH).
* rebind_after_fallback -- the quopri SHAPE: the handler binds the
  imported names to None and later code tests them (MATCH). The
  present-module twin of this row -- where CPython succeeds and only
  RESULT equivalence can be asserted -- is the 2.5 battery
  (harness/scripts/import_bisect_fallback.py).
* star guarded -- `from zzz import *` under the guard: the raise fires
  before any binding, the handler observes it (MATCH).

The uncaught/refused rows live as their own scripts (an uncaught raise
ends a file): harness/scripts/import_missing_uncaught.py,
import_star_missing.py, import_not_top_level.py.
"""

# happy_fallback: the guard catches the model's raise -- and CPython's,
# because the module is genuinely absent from the pinned platform
try:
    from zzz_no_such_module import fast_add
except ImportError:
    fast_add = None

if fast_add is None:
    print("fallback")


def add(a, b):
    return a + b


# rebind_after_fallback (the quopri shape): handler binds BOTH names,
# later top-level code tests them -- the bindings must be live globals
# (the script view deliberately drops the structured import, so the
# reads resolve through World.globals)
try:
    from zzz_no_such_module import a2b_qp, b2a_qp
except ImportError:
    a2b_qp = None
    b2a_qp = None

if a2b_qp is None and b2a_qp is None:
    print("pure path")

# star_missing, guarded arm: the raise fires before any binding
try:
    from zzz_no_such_module import *
except ImportError:
    print("star caught")

print(add(2, 3))
