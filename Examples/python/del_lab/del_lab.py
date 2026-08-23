"""del_lab -- the `del <name>` acceptance set (docs/memory-model.md
paragraph "the del statement"; docs/backlog.md paragraph "del RECONCILED
with the one pipeline").

FUNCTION scope is the recorded slice: `del` of a bound local is a pure
locals rewrite (`Env.remove` -- no World field moves), the effect is
PARTIAL left to right, and the read-after-del hazard is closed by the
extractor CENSUS (clause 2: any Load of a del'd name refuses the whole
function), never by a fabricated UnboundLocalError. The stated
over-refusals are pinned here so their cost stays visible:
`rebind_after` and `loop_del` are programs CPython ACCEPTS that the
census refuses (name-set intersection, deliberately not a liveness
analysis).

Runtime refusals (the census cannot see boundness): `del` of a
module-global NAME (CPython localises it and raises UnboundLocalError),
`del` of a never-bound name, double `del` -- all LOUD, never a guessed
exception class. Shape refusals (clause 4): `del d[k]` and `del o.attr`
are measured second tables and stay Unsupported at extraction.

MODULE-scope `del` is the script surface's arm and is pinned by the
script corpus rows (del_global_script / del_never_script /
del_trailing_script / del_partial_script and the loud trio), not here:
on the closed-function surface a top-level `del` refuses at module init
(empty init locals) and poisons its targets -- `gnum` below exists so
`del_global` has a real module global to fail on.
"""

gnum = 7


def keep(n):
    # in tier: del of a local never read after
    x = n + 1
    del x
    return n * 2


def del_param(n):
    # in tier: a parameter is an ordinary local
    del n
    return 0


def del_two(n):
    # in tier: two unread locals, one statement, left to right
    x = n
    y = n
    del x, y
    return 7


def cond_del(n):
    # in tier: the del is conditional, and nothing reads x after it
    x = n
    if n > 0:
        del x
    return n


def read_after(n):
    # census clause 2: the read at `return x` refuses the function
    # (CPython: UnboundLocalError at runtime)
    x = n
    del x
    return x


def rebind_after(n):
    # the STATED over-refusal: CPython returns 99, the census refuses
    # (the rebind does not clear the name-set intersection)
    x = n
    del x
    x = 99
    return x


def loop_del(n):
    # the loop del-then-rebind row: CPython answers 6 for n = 3, the
    # census refuses (same recorded over-refusal)
    t = 0
    for i in range(n):
        x = i
        del x
        x = i * 2
        t = t + x
    return t


def del_global():
    # runtime refusal: `del` LOCALISES gnum (whole-body rule), so
    # CPython raises UnboundLocalError -- the model's locals miss is
    # loud, never a guessed class
    del gnum
    return 0


def del_never():
    # runtime refusal: never-bound name
    del nope
    return 0


def double_del(n):
    # runtime refusal on the SECOND del (the first really removed x --
    # the partial, threaded state)
    x = n
    del x
    del x
    return 0


def del_sub():
    # LANDED (§del): clause 4 now admits a single subscript target and
    # ingestion rewrites it to `<dictdel>(d, k)`. This row was the shape
    # refusal; it is now the shape's acceptance.
    d = {1: 2}
    del d[1]
    return 0


def del_attr(o):
    # shape refusal (clause 4): attribute target stays Unsupported
    del o.attr
    return 0
