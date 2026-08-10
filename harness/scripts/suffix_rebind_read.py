"""Refusal row (the stale-table hazard): the live suffix REBINDS a
prefix-bound module global a function body reads. CPython makes `z = z + 41`
a module global, so readz() answers 42; leanpy's suffix bindings land in
the script's locals, invisible to function frames, so running this would
answer a stale 1 — `suffixConsistent` refuses the whole script loudly."""

z = 1


def readz():
    return z


print(readz())
z = z + 41
print(readz())
