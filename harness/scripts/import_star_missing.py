"""Pass 0 (docs/memory-model.md paragraph "Import forms (Pass 0)"),
star_missing row, UNGUARDED arm: `from zzz import *` of an
inventory-absent module raises before any binding -- same
`ModuleNotFoundError`, same exit 1, class line CPython-identical. (The
guarded star arm lives in Examples/python/import_lab.)
REBUILD-WINDOW: measured when the shared rebuild lands."""

print("start")
from zzz_no_such_module import *
print("unreached")
