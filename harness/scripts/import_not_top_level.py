"""Pass 0 (docs/memory-model.md paragraph "Import forms (Pass 0)"),
not_top_level row: a FUNCTION-BODY from-import is outside the admitted
shape (module top level only), so the extractor keeps the Unsupported
fallthrough and the model refuses LOUDLY at the call -- exit 3, never a
fake ImportError for a statement CPython would also raise on here only
because the module is absent. The refusal channel is the point: the
model does not pretend to know what a function-body import does.
REBUILD-WINDOW: expect stays "unsupported"."""


def f():
    from zzz_no_such_module import x
    return 1


print(f())
