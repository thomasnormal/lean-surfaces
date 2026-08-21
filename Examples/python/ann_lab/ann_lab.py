"""Annotated assignment (`AnnAssign`) — §L49 rung 2.

docs/memory-model.md paragraph "annotated assignment" is the contract;
docs/completeness.md rung 2 is the pricing. Every function here runs
differentially against CPython 3.9 (harness/cases.json).

THE MEASURED SPLIT. In a FUNCTION BODY PEP 526 does not evaluate the
annotation at all, so `x: T = v` at a plain-name target is an ordinary
assignment — exactly, with no condition on `T`. The rows below prove that
by annotating with expressions that would RAISE if anyone evaluated them.
At MODULE and CLASS scope the annotation IS evaluated and
`__annotations__` is written, so those stay loud (the script row
`harness/scripts/ann_module_script.py`), and so does the value-less form,
which binds nothing yet LOCALISES its name.
"""

g = 5


def ann_value(n):
    x: int = n + 1
    return x


def ann_undefined_ann(n):
    # the annotation names something that does not exist; CPython does not
    # look, so neither does the model
    x: NoSuchType = n
    return x


def ann_raising_ann(n):
    # sharper: an annotation that would RAISE if it were evaluated. This is
    # the row that makes "the annotation is not evaluated" falsifiable
    # rather than asserted
    x: (1 // 0) = n
    return x


def ann_subscript_ann(n):
    # the modern spelling, whose annotation is a subscript of an undefined
    # name -- still never evaluated
    x: List[int] = n
    return x


def ann_str_ann(n):
    # a string annotation (the forward-reference spelling)
    x: "SomeForwardRef" = n
    return x


def ann_shadow_builtin(n):
    # the TARGET shadows a builtin; the annotation names one. Neither is
    # special: this is an ordinary local assignment
    len: int = n
    return len


def ann_reassign(n):
    x: int = 1
    x = x + n
    return x


def ann_nested(n):
    # the rewrite has to reach statements nested in compound bodies, which
    # is what the extractor's `func_scope` flag is threaded for
    t = 0
    for i in [1, 2]:
        y: int = i
        t = t + y
    if n > 0:
        z: int = 10
        t = t + z
    while t < 0:
        w: int = 1
        t = t + w
    return t


def ann_aug(n):
    total: int = 0
    for i in range(n):
        total += i
    return total


def ann_novalue(n):
    # LOUD: `x: int` binds nothing. Dropping it would be harmless HERE and
    # a silent wrong answer in `ann_novalue_shadows_global`, so the shape
    # is refused as a shape, not case by case
    x: int
    return n


def ann_novalue_read(n):
    # LOUD: CPython raises UnboundLocalError -- the name is local because
    # the annotation localised it, and nothing ever bound it
    x: int
    return x


def ann_novalue_shadows_global(n):
    # LOUD, and this is THE row the refusal exists for: `g` is a module
    # global holding 5, and the value-less annotation makes it LOCAL for
    # the whole body, so CPython raises UnboundLocalError. A model that
    # dropped the statement would read the global and answer 5 --
    # a silent wrong answer, not a refusal
    g: int
    return g


def ann_attr_target(n):
    # LOUD: a non-simple target (`simple == 0`) gets no `__annotations__`
    # entry but its annotation IS still evaluated
    d = {}
    d["k"]: int = n
    return d["k"]
