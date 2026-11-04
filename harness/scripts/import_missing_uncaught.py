"""Pass 0 (docs/memory-model.md paragraph "Import forms (Pass 0)"),
missing_uncaught row: an UNGUARDED from-import of an inventory-absent
module. The raise is CPython's own behavior, so both sides print
"before", exit 1, and report the same class line --
`ModuleNotFoundError: No module named 'zzz_no_such_module'` (the model
carries the exact message: errName/errMessage, Main.lean).
REBUILD-WINDOW: registered with the implementation, measured when the
shared rebuild lands."""

print("before")
from zzz_no_such_module import x
print("unreached")
