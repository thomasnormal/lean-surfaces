"""leanpy corpus: THE THIRD DOOR — a DECORATED METHOD is a creation effect.

The refusal row, and the contrast is the whole point: under CPython this
program prints

    registered m
    after

because `@log` is CALLED while the class body runs, at the `class`
statement. The model builds its `ClassDefn` at ingestion and executes no
class body at all, so before 2026-08-14 it printed only "after" — a WRONG
ANSWER, not a refusal, and the third way into the hole `creationPure`
exists to close. The first two doors were a class-body statement
(`cls_effect_script.py`) and a base expression; both were shut, and this
one stayed open because the extractor's body loop and `classBodyStmtPure`
each skipped a `FunctionDef` UNCONDITIONALLY, decorator list and all.

`ClassDefn.creationPure` is now false for a class with any decorated
method, so `runScript` refuses the whole script loudly rather than skip
the decorator's effect (docs/memory-model.md §class semantics, "Class
CREATION is an effect").

Found by `harness/class_census.py`: 15 such classes in 14 files of the
pinned 3.9 Lib, 2 of them in files this admission was passing. Every one
of the 15 decorates with property/setter/classmethod/staticmethod, which
happen to have no creation-time effect — the model was lucky, not sound,
and this row is the unlucky case written down.
"""


def log(f):
    print("registered " + f.__name__)
    return f


class C:
    @log
    def m(self):
        return 1


print("after")
