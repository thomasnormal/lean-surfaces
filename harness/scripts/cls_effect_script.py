"""leanpy corpus: CLASS CREATION IS AN EFFECT — the refusal row.

CPython runs a class body at the `class` statement, so this program
prints "creating C" BEFORE "after". The model builds its `ClassDefn` at
ingestion and executes no class body at all; skipping the print silently
would be a wrong answer, so `runScript` refuses the whole script loudly
(`ClassDefn.creationPure`, docs/memory-model.md §class creation).

This row exists because `tools/leanpy` found the hole: it was a MISMATCH
against CPython before the guard, the only silent divergence the first
completeness survey turned up.
"""


class C:
    print("creating C")
    x = 1


print("after")
