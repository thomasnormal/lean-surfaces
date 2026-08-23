#!/usr/bin/env python3
"""refusal_census.py — the REFUSAL SURFACE, measured (docs/completeness.md).

    python3 harness/refusal_census.py [--grammar] [--whitelist] [--scripts]
                                      [--no-build] [--runner CMD]
                                      [--json OUT] [--keep DIR]

Three questions, three modes, one law: **every census claim is a run**,
never a reading of the source.

``--grammar`` — THE GRAMMAR CENSUS. One minimal witness per production of
  CPython 3.9's ``ast`` grammar (25 statements, 27 expressions, 13 binary
  / 4 unary / 10 comparison / 2 boolean operators, plus the four
  ``Constant`` payload types the extractor forks on). Each witness is a
  whole PROGRAM: it is extracted, run under the pinned oracle, run
  through the model, and the two are compared. The verdict is
  ``MATCH`` / ``REFUSE`` / ``DIVERGE`` / ``TIMEOUT`` / ``EXTRACT``, and
  the refusal MESSAGE is printed beside it — so the census reports which
  layer refused (extractor, ingestion, or interpreter) in the only way
  that cannot be wrong.

  WHAT A `MATCH` DOES AND DOES NOT CLAIM. It claims: this production is
  reachable and the model agreed with CPython on this witness. It does
  NOT claim the production is wholly in tier — `op.Mult` matches on
  `2 * 3` and refuses on `"ab" * 3`. The grammar census is a LOWER bound
  on coverage; the refusal-message tables below are the upper bound. Both
  are needed and neither substitutes for the other (docs/backlog.md §L14:
  a statement-level `Unsupported` count is not an ingestion verdict —
  run the thing).

``--whitelist`` — THE WHITELIST CENSUS. `harness/cases.json`'s
  ``"expect": "unsupported"`` rows are the closed-function surface's
  recorded gaps. This mode runs them all through one ``--batch`` process,
  reads the refusal MESSAGE off each, and buckets them by the construct
  CLASS recorded in ``WHITELIST_CLASS`` below. A whitelisted row with no
  class entry is an ERROR: the census must cover the whole whitelist, so
  a new gap cannot be added without being classified.

``--scripts`` — the same for `harness/scripts.json`'s
  ``"expect": "unsupported"`` rows (the whole-program surface).

Exit status is 1 on any DRIFT: a witness whose measured verdict differs
from the recorded one, a whitelisted row with no class, or a class table
that cannot be built. Drift is the point — this file is a census, and a
census that is not re-measurable is a story.

Nothing is written beside any source: the witnesses are written to a
temporary directory (``--keep DIR`` to inspect them) and their envelopes
go to the shared leanpy cache, exactly as `harness/script_corpus.py` does.

Python 3.9 compatible.
"""

import argparse
import json
import os
import subprocess
import sys
import tempfile

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def _reexec_under_pinned_frontend():
    """Both ends pinned, the `harness/script_corpus.py` fix verbatim: the
    witnesses below use 3.8+ syntax (walrus, f-strings) and 3.9 is the
    version the tier is specified against, so the interpreter that PARSES
    them and the interpreter that RUNS them must both be the pin."""
    if os.environ.get("LEANPY_NO_REEXEC"):
        return
    want = os.environ.get("LEANPY_FRONTEND") or "python3.9"
    if sys.version_info[:2] == (3, 9) and not os.environ.get("LEANPY_FRONTEND"):
        return
    from shutil import which
    exe = which(want)
    if exe is None:
        print("harness/refusal_census.py: WARNING the pinned frontend %r is "
              "not installed; extracting with %s instead — the census would "
              "measure a different grammar" % (want, sys.version.split()[0]),
              file=sys.stderr)
        return
    if os.path.realpath(exe) == os.path.realpath(sys.executable):
        return
    os.environ["LEANPY_NO_REEXEC"] = "1"
    os.execv(exe, [exe, os.path.abspath(__file__)] + sys.argv[1:])


_reexec_under_pinned_frontend()

sys.path.insert(0, os.path.join(REPO_ROOT, "harness"))
# `harness/leanpy_survey.py` owns the whole-program verdict vocabulary this
# census reports in — the oracle pin, the batch stdout join, the exception
# CLASS comparison and the leanpy module load. Reuse them rather than
# growing a second copy that can drift from the survey's own verdicts.
import leanpy_survey  # noqa: E402

leanpy = leanpy_survey.leanpy
lean_stdout = leanpy_survey.lean_stdout
cpython_exc_class = leanpy_survey.cpython_exc_class
ORACLE = os.environ.get("LEANPY_CPYTHON") or leanpy_survey.default_oracle()


# ---------------------------------------------------------------------------
# THE GRAMMAR WITNESSES
#
# One per production of the 3.9 ASDL grammar, keyed `<sort>.<Production>`.
# `expect` is the MEASURED verdict at the pass that recorded it, never a
# prediction; `note` says what the verdict means for arbitrary Python.
# ---------------------------------------------------------------------------

W = []

# Which expectation column `--grammar` checks; set from --target in main().
EXPECT_KEY = "expect"


def w(wid, src, expect, note):
    """`mono` is the expectation under `--target monadic`, when it DIFFERS.

    The rebuild is not required to be a clone: inch 3a opens the live dict
    cursor on the monadic definition ONLY (the trunk gains a refuse arm by
    the no-backwards-compat ruling), so a witness may legitimately refuse on
    one interpreter and run on the other. Encoding that here keeps the census
    a scoreboard for BOTH rather than a parity check that has to be switched
    off the moment the two diverge on purpose."""
    W.append({"id": wid, "src": src.lstrip("\n"), "expect": expect,
              "note": note})


# --- stmt (25 productions) -------------------------------------------------
w("stmt.FunctionDef", """
def f(x):
    return x + 1
print(f(1))
""", "MATCH", "plain positional def")
w("stmt.AsyncFunctionDef", """
async def f():
    return 1
print(0)
""", "REFUSE", "the whole async sort")
w("stmt.ClassDef", """
class C:
    def __init__(self, x):
        self.x = x
print(C(3).x)
""", "MATCH", "H3 class tier, default protocol only")
w("stmt.Return", """
def f():
    return 7
print(f())
""", "MATCH", "")
w("stmt.Delete", """
x = 1
del x
print(2)
""", "MATCH", "bare-name del at module scope")
w("stmt.Assign", """
x = 1
print(x)
""", "MATCH", "")
w("stmt.AugAssign", """
x = 1
x += 2
print(x)
""", "MATCH", "")
w("stmt.AnnAssign", """
x: int = 1
print(x)
""", "REFUSE",
  "MODULE scope: the annotation IS evaluated here and `__annotations__` is "
  "written, so §L49 rung 2's rewrite deliberately stops short of it")
w("stmt.AnnAssign-local", """
def f(n):
    x: int = n + 1
    return x
print(f(1))
""", "MATCH",
  "FUNCTION scope: PEP 526 never evaluates the annotation, so this is an "
  "ordinary assign — was REFUSE, landed by §L49 rung 2")
w("stmt.AnnAssign-novalue", """
def f(n):
    x: int
    return n
print(f(1))
""", "REFUSE",
  "`x: int` binds nothing yet LOCALISES the name; dropping it would read a "
  "module global where CPython raises UnboundLocalError")
w("stmt.For", """
for i in [1, 2]:
    print(i)
""", "MATCH", "")
w("stmt.AsyncFor", """
async def f(xs):
    async for x in xs:
        print(x)
print(0)
""", "REFUSE", "rides the async sort")
w("stmt.While", """
i = 0
while i < 2:
    print(i)
    i += 1
""", "MATCH", "")
w("stmt.If", """
if 1 < 2:
    print(1)
else:
    print(2)
""", "MATCH", "")
w("stmt.With", """
class C:
    def __enter__(self):
        return 1
    def __exit__(self, a, b, c):
        return False
with C() as v:
    print(v)
""", "REFUSE", "the context-manager protocol")
w("stmt.AsyncWith", """
async def f(c):
    async with c as v:
        print(v)
print(0)
""", "REFUSE", "rides the async sort")
w("stmt.Raise", """
raise ValueError("boom")
""", "REFUSE", "no exception VALUES; PyErr is not a first-class object")
w("stmt.Try", """
try:
    print(1)
except ValueError:
    print(2)
""", "REFUSE", "the handler sort")
w("stmt.Assert", """
assert 1 == 1
print("ok")
""", "MATCH", "assert is in tier; AssertionError is not catchable")
w("stmt.Import", """
import math
print(1)
""", "REFUSE", "no module system (docs/backlog.md §the import ceiling)")
w("stmt.ImportFrom", """
from math import sqrt
print(1)
""", "REFUSE", "same; the benign whitelist is the only admission")
w("stmt.Global", """
g = 1
def f():
    global g
    g = 2
f()
print(g)
""", "REFUSE", "no write path from a frame to module globals")
w("stmt.Nonlocal", """
def outer():
    c = 1
    def inner():
        nonlocal c
        c = c + 1
    inner()
    return c
print(outer())
""", "REFUSE", "closure cells are read-at-call, never written back")
w("stmt.Expr", """
print(1)
""", "MATCH", "")
w("stmt.Pass", """
pass
print(1)
""", "MATCH", "")
w("stmt.Break", """
for i in [1, 2]:
    break
print(i)
""", "MATCH", "")
w("stmt.Continue", """
t = 0
for i in [1, 2]:
    if i == 1:
        continue
    t = t + i
print(t)
""", "MATCH", "")

# --- expr (27 productions) -------------------------------------------------
w("expr.BoolOp", """
print(1 and 2)
""", "MATCH", "")
w("expr.NamedExpr", """
if (n := 5) > 1:
    print(n)
""", "MATCH", "§L14's walrus, general expression position")
w("expr.BinOp", """
print(1 + 2)
""", "MATCH", "")
w("expr.UnaryOp", """
print(-1)
""", "MATCH", "")
w("expr.Lambda", """
f = lambda x: x + 1
print(f(1))
""", "MATCH", "module-scope single-target lambda only")
w("expr.IfExp", """
print(1 if 2 > 1 else 3)
""", "MATCH", "")
w("expr.Dict", """
print({1: 2})
""", "MATCH", "")
w("expr.Set", """
print(len({1, 2}))
""", "REFUSE", "a set display; hash order is never guessed")
w("expr.ListComp", """
print([x + 1 for x in [1, 2]])
""", "MATCH", "desugared to list(genexp) at ingestion")
w("expr.SetComp", """
print(len({x for x in [1, 2]}))
""", "REFUSE", "")
w("expr.DictComp", """
print({x: x for x in [1, 2]})
""", "REFUSE", "")
w("expr.GeneratorExp", """
print(sum(x for x in [1, 2]))
""", "MATCH", "lowered to a synthesized generator function")
w("expr.Await", """
async def f(c):
    return await c
print(0)
""", "REFUSE", "rides the async sort")
w("expr.Yield", """
def g():
    yield 1
    yield 2
print(sum(g()))
""", "MATCH", "statement position only")
w("expr.YieldFrom", """
def g():
    yield from [1, 2]
print(sum(g()))
""", "MATCH", "inlined at ingestion")
w("expr.Compare", """
print(1 < 2)
""", "MATCH", "")
w("expr.Call", """
print(len([1, 2]))
""", "MATCH", "")
w("expr.JoinedStr", """
n = 3
print(f"{n}")
""", "MATCH", "bare replacement fields only")
w("expr.FormattedValue", """
n = 3
print(f"a{n}b")
""", "MATCH", "same node; the conversion/spec slots are the gap")
w("expr.Constant", """
print(1, "a", True, None)
""", "MATCH", "the int/str/bool/None inventory")
w("expr.Attribute", """
class C:
    def __init__(self):
        self.x = 1
print(C().x)
""", "MATCH", "")
w("expr.Subscript", """
print([1, 2][0])
""", "MATCH", "")
w("expr.Starred", """
a = [1, 2]
print([*a])
""", "MATCH", "display position only")
w("expr.Name", """
x = 1
print(x)
""", "MATCH", "")
w("expr.List", """
print([1, 2])
""", "MATCH", "")
w("expr.Tuple", """
print((1, 2))
""", "MATCH", "")
w("expr.Slice", """
print("abcd"[1:3])
""", "MATCH", "str receivers; list/tuple slices allocate and refuse")

# --- dict iteration: rung 3's surface, one witness per consumer ------------
# All REFUSE today. They are written as the ACCEPTANCE BATTERY for the rung:
# each flips to MATCH as its consumer lands, and the two live-cursor rows
# below carry the semantics the census measured (docs/memory-model.md
# paragraph "dict iteration").
w("dict.for", """
d = {2: 'b', 1: 'a'}
for k in d:
    print(k)
""", "MATCH",
  "the live cursor — inch 3a. Was REFUSE/mono=MATCH while there were two "
  "interpreters; there is one now, so the opened answer is THE answer")
w("dict.list", """
print(list({2: 'b', 1: 'a'}))
""", "MATCH", "a DRAINING consumer: no mutation window — landed by §L53 rung 3b")
w("dict.tuple", """
print(tuple({2: 'b', 1: 'a'}))
""", "MATCH", "landed by §L53 rung 3b")
w("dict.sorted", """
print(sorted({2: 'b', 1: 'a'}))
""", "MATCH", "landed by §L53 rung 3b")
w("dict.sum", """
print(sum({2: 20, 1: 10}))
""", "MATCH", "landed by §L53 rung 3b")
w("dict.max", """
print(max({2: 'b', 1: 'a'}))
""", "MATCH", "landed by §L53 rung 3b")
w("dict.star", """
d = {2: 'b', 1: 'a'}
print([*d])
""", "MATCH", "landed by §L53 rung 3b")
w("dict.for-in-function", """
def f():
    d = {2: 'b', 1: 'a', 5: 'c'}
    out = []
    for k in d:
        if k == 1:
            continue
        out.append(k)
        if len(out) == 2:
            break
    return tuple(out)
print(f())
""", "MATCH",
  "the cursor at FUNCTION scope — execGen's arm, and it exercises `break` "
  "and `continue` through the new frame (which is why `genBreak`/"
  "`genContinue` had to treat `forDict` as a LOOP frame, not bookkeeping)")
w("dict.for-keys", """
def f():
    d = {3: 'c', 1: 'a'}
    out = []
    for k in d.keys():
        out.append(k)
    return tuple(out)
print(f())
""", "MATCH", "`for k in d.keys()` at function scope — inch 3c-i-a")
w("dict.for-values", """
def f():
    d = {3: 'c', 1: 'a'}
    out = []
    for v in d.values():
        out.append(v)
    return tuple(out)
print(f())
""", "MATCH", "`for v in d.values()` — the VALUES view, whose element is the "
  "value, not the key")
w("dict.values", """
d = {2: 'b', 1: 'a'}
print(sorted(d.values()))
""", "REFUSE", "the VALUES view, consumed immediately — inch 3c-i")
w("dict.items-consumed", """
d = {2: 'b', 1: 'a'}
print(list(d.items()))
""", "REFUSE", "the ITEMS view, consumed immediately — inch 3c-i")
w("dict.view-escapes", """
d = {1: 'a'}
k = d.keys()
d[2] = 'b'
print(list(k))
""", "REFUSE",
  "THE 3c-ii MARKER: a view is a LIVE first-class object, not a snapshot — "
  "CPython prints [1, 2] because `k` still sees the dict. Consuming forms "
  "(3c-i) never need that; this one does, and it is what an `Obj.dictView` "
  "would buy")
w("dict.values-identity-eq", """
d = {1: 'a'}
print(d.values() == d.values())
""", "REFUSE",
  "THE TRAP, measured: CPython answers FALSE. A values view defines no "
  "equality, so it compares by IDENTITY — while `d.keys() == {1}` is True "
  "by SET equality. A model that treated the three views alike would be "
  "silently wrong here, in the direction that looks most reasonable")
w("dict.keys-set-algebra", """
d = {2: 'b', 1: 'a'}
print(sorted(d.keys() & {1, 9}))
""", "REFUSE",
  "keys/items are SET-LIKE (`&`, `|`, `-`, `^` answer a set); values are "
  "NOT (`d.values() & {1}` is a TypeError). Two inventories, not one")
w("dict.enumerate", """
d = {2: 'b', 1: 'a'}
for i, k in enumerate(d):
    print(i, k)
""", "REFUSE", "inch 3c")
w("dict.keys", """
print(list({2: 'b', 1: 'a'}.keys()))
""", "REFUSE", "the view methods — inch 3c")
w("dict.items", """
d = {2: 'b', 1: 'a'}
for k, v in d.items():
    print(k, v)
""", "MATCH",
  "MEASURED CORRECTION — the live cursor is already BUILT at MODULE scope "
  "(the script executor's `.items()` shell). Rung 3 is an EXTENSION, not a "
  "construction")
w("dict.items-in-function", """
def f():
    d = {2: 'b', 1: 'a'}
    t = 0
    for k, v in d.items():
        t = t + k
    return t
print(f())
""", "MATCH",
  "the SAME loop inside a function — 3a gave the bare-key form a cursor at "
  "every scope; 3c-i-a gives the VIEW forms one too")
w("dict.items-grow", """
d = {1: 1}
for k, v in d.items():
    d[k + 5] = 0
print('unreachable')
""", "MATCH",
  "MEASURED: the module-scope shell already raises CPython's RuntimeError "
  "VERBATIM ('dictionary changed size during iteration') — the size guard "
  "is faithful TODAY, so inch 3a inherits it rather than inventing it")
w("dict.items-update", """
d = {1: 1, 2: 2}
for k, v in d.items():
    d[k] = v * 100
print(d[1], d[2])
""", "MATCH", "the admissible regime, already exact at module scope")
w("dict.update-value-during-iter", """
d = {1: 1, 2: 2}
for k in d:
    d[k] = d[k] * 100
print(d[1], d[2])
""", "MATCH",
  "MEASURED admissible: updating an EXISTING key's value during iteration "
  "is fine in CPython — the regime inch 3a reproduces exactly")
w("dict.grow-during-iter", """
d = {1: 1}
for k in d:
    d[k + 10] = 0
print('unreachable')
""", "MATCH",
  "MEASURED: CPython raises RuntimeError('dictionary changed size during "
  "iteration') at the NEXT step — inch 3a reproduces THAT, not refuses it")
w("dict.churn-during-iter", """
d = {1: 1, 2: 2, 3: 3}
for k in d:
    if k == 2:
        del d[1]
        d[99] = 9
print('unreachable')
""", "REFUSE",
  "MEASURED, and a CROSS-RUNG dependency: this witness reports `del d[k]`, "
  "which refuses FIRST, so the hazard is unreachable today — and the day "
  "dict deletion lands it becomes required. A SAME-SIZE key-set change is "
  "storage-layout dependent: CPython raises a SECOND, different "
  "RuntimeError('dictionary keys changed during iteration') here, and "
  "moving the deletion ahead of the cursor "
  "makes it answer [1, 2, 99] with no error at all. Permanently LOUD.")

# --- Constant payloads the extractor forks on ------------------------------
w("const.float", """
print(1.5)
""", "REFUSE", "NO FLOATS AT ALL — the single largest gap")
w("const.bytes", """
print(len(b"ab"))
""", "REFUSE", "no bytes type")
w("const.complex", """
print(1j)
""", "REFUSE", "")
w("const.ellipsis", """
x = ...
print(1)
""", "REFUSE", "")

# --- operator (13) ---------------------------------------------------------
w("op.Add", "print(1 + 2)\n", "MATCH", "")
w("op.Sub", "print(3 - 1)\n", "MATCH", "")
w("op.Mult", "print(2 * 3)\n", "MATCH", "int only; str/list repetition refuses")
w("op.Div", "print(6 / 2)\n", "REFUSE", "true division makes a float")
w("op.FloorDiv", "print(7 // 2)\n", "MATCH", "Int.fdiv")
w("op.Mod", "print(7 % 2)\n", "MATCH", "Int.fmod; `str % args` is a second tier")
w("op.Pow", "print(2 ** 3)\n", "MATCH",
  "MEASURED CORRECTION: `**` is in tier; only the float-valued negative "
  "exponent refuses (op.Pow-negative)")
w("op.Pow-negative", "print(2 ** -1)\n", "REFUSE",
  "the boundary op.Pow's witness does not reach")
w("op.LShift", "print(1 << 4)\n", "MATCH", "budget-capped shift width")
w("op.RShift", "print(16 >> 2)\n", "MATCH",
  "was REFUSE; §L39 rung 1 landed it (op.RShift-budget is its edge)")
w("op.RShift-budget", "print(1 >> 10 ** 30)\n", "REFUSE",
  "`<<`'s budget, for `<<`'s reason: forming 2**b would abort")
w("op.BitOr", "print(5 | 2)\n", "MATCH", "")
w("op.BitXor", "print(5 ^ 3)\n", "MATCH",
  "was REFUSE — the one witness that found the whole rung; §L39 landed it")
w("op.BitAnd", "print(5 & 3)\n", "MATCH", "")
w("op.MatMult", "print(1 @ 2)\n", "REFUSE",
  "FAITHFUL: no operand type in or out of tier has it (CPython TypeError)")

# --- unaryop (4) -----------------------------------------------------------
w("op.UAdd", "print(+3)\n", "MATCH", "was REFUSE; §L39 rung 1")
w("op.USub", "print(-3)\n", "MATCH", "")
w("op.Not", "print(not 0)\n", "MATCH", "")
w("op.Invert", "print(~5)\n", "MATCH", "was REFUSE; §L39 rung 1")

# --- cmpop (10) ------------------------------------------------------------
w("op.Eq", "print(1 == 1)\n", "MATCH", "")
w("op.NotEq", "print(1 != 2)\n", "MATCH", "")
w("op.Lt", "print(1 < 2)\n", "MATCH", "")
w("op.LtE", "print(1 <= 1)\n", "MATCH", "")
w("op.Gt", "print(2 > 1)\n", "MATCH", "")
w("op.GtE", "print(2 >= 2)\n", "MATCH", "")
w("op.Is", "print([] is [])\n", "MATCH", "refs by address; two immediates refuse")
w("op.IsNot", "print([] is not [])\n", "MATCH", "")
w("op.In", "print(1 in [1, 2])\n", "MATCH", "")
w("op.NotIn", "print(3 not in [1, 2])\n", "MATCH", "")

# --- boolop (2) ------------------------------------------------------------
w("op.And", "print(1 and 2)\n", "MATCH", "")
w("op.Or", "print(0 or 2)\n", "MATCH", "")


# ---------------------------------------------------------------------------
# THE WHITELIST CLASSIFICATION
#
# `<example>::<function>` -> construct class, for every
# `"expect": "unsupported"` row of harness/cases.json. Unclassified rows
# fail the run: the census covers the whole whitelist or it is not one.
# ---------------------------------------------------------------------------

WHITELIST_CLASS = {
    "arith::powi": "op.Pow",
    "tut_06::true_div": "op.Div",
    "rsa_inverse::inverse": "exc.raise",
    "dict_lab::ret_dict": "boundary.heap-value",
    "dict_lab::ret_tuple_with_dict": "boundary.heap-value",
    "dict_lab::int_is": "op.Is-immediates",
    "sf_hist::push": "boundary.list-mutation",
    "sf_hist::rotate_scores": "boundary.list-mutation",
    "cls_lab::attr_on_int": "attr.on-scalar",
    "cls_lab::weird_eq": "class.dunder-protocol",
    "cls_lab::sub_inherits": "class.inheritance",
    "cls_lab::class_as_value": "firstclass.callable",
    "cls_lab::aug_attr_list": "augassign.container-attr",
    "cls_lab::unpack_subscript_elem": "assign.non-name-target",
    "cls_lab::chain_attr_first": "assign.non-name-target",
    "sf_position::mk_move": "boundary.namedtuple",
    "sf_position::asdict_is_loud": "namedtuple.protocol",
    "sf_position::fields_are_loud": "namedtuple.protocol",
    "sf_position::mirror_is_loud": "boundary.namedtuple",
    "sf_position::bound_method_is_loud": "firstclass.callable",
    "str_lab::cast_int": "builtin.int-of-str",
    "str_lab::swap": "str.non-ascii",
    "str_lab::isup": "str.non-ascii",
    "str_lab::list_slice_is_loud": "slice.allocating",
    "str_lab::idx_start_is_loud": "strmethod.arity",
    "str_lab::fmt_nonascii_r": "str.non-ascii",
    "str_lab::fmt_width": "format.percent-minilanguage",
    "str_lab::fmt_hex": "format.percent-minilanguage",
    "str_lab::fmt_bad": "format.percent-minilanguage",
    "str_lab::fmt_trailing": "format.percent-minilanguage",
    "str_lab::fmt_container": "format.percent-heap-operand",
    "str_lab::fmt_mapping": "format.percent-heap-operand",
    "str_lab::fmt_seq_arg": "format.percent-heap-operand",
    "str_lab::fmt_dict_leftover": "format.percent-heap-operand",
    "iter_lab::chr_surrogate": "str.surrogate",
    "gen_lab::walrus_leak": "genexp.lowering-admission",
    "gen_lab::upto": "boundary.generator",
    "gen_lab::gen_at_boundary": "boundary.generator",
    "gen_lab::send_is_loud": "generator.send-throw-close",
    "gen_lab::gen_assigned_lazy": "genexp.lowering-admission",
    "gen_lab::drain_unbound": "genexp.lowering-admission",
    "gen_lab::yf_leak_drive": "genexp.lowering-admission",
    "exc_lab::time_live": "clock.underrun",
    "exc_lab::as_binding": "exc.handler",
    "exc_lab::finally_clause": "exc.finally",
    "exc_lab::else_clause": "exc.handler",
    "exc_lab::bare_except": "exc.handler",
    "exc_lab::multi_handler": "exc.handler",
    "exc_lab::tuple_handler": "exc.handler",
    "exc_lab::except_exception": "exc.handler",
    "exc_lab::except_builtin": "exc.handler",
    "exc_lab::raise_args": "exc.raise",
    "exc_lab::raise_bare": "exc.raise",
    "exc_lab::raise_value": "exc.raise",
    "exc_lab::raise_from": "exc.raise",
    "exc_lab::raise_shadowed": "exc.raise",
    "exc_lab::exc_as_value": "firstclass.callable",
    "exc_lab::drive_yield_under_try": "exc.handler",
    "kw_lab::ntuple_kw": "kwargs.callee-kind",
    "kw_lab::builtin_kw": "kwargs.callee-kind",
    "drain_lab::sorted_mixed": "order.mixed-type",
    "closure_lab::uses_nonlocal": "stmt.Nonlocal",
    "closure_lab::def_in_loop": "closure.admission",
    "closure_lab::early_call": "closure.admission",
    "closure_lab::rec_nested_name": "closure.admission",
    "closure_lab::cell_escapes": "closure.admission",
    "closure_lab::gen_cell_after_call": "closure.admission",
    "set_lab::iter_is_loud": "set.order",
    "set_lab::sorted_is_loud": "set.order",
    "seq_lab::band_set": "set.order",
    "seq_lab::range_eq": "range.observation",
    "seq_lab::range_index": "range.observation",
    "seq_lab::range_in": "range.observation",
    "seq_lab::range_boundary": "boundary.range",
    "seq_lab::range_unpack": "range.observation",
    "seq_lab::list_slice_loud": "slice.allocating",
    "seq_lab::str_repeat_loud": "op.Mult-repetition",
    "seq_lab::shl": "op.LShift-budget",
    "seq_lab::shr": "op.LShift-budget",
    "clock_lab::armed": "exc.handler",
    "clock_lab::read_clock": "clock.underrun",
    "clock_lab::shadowed": "attr.on-scalar",
    "clock_lab::call_with_arg": "clock.arity",
    "star_lab::star_call": "starred.position",
    "star_lab::star_set": "set.order",
    "star_lab::star_target": "starred.position",
    "star_lab::star_for": "starred.position",
    "star_shadow::shadowed": "shadow.module-census",
    "star_shadow::elsewhere": "shadow.module-census",
    "ann_lab::ann_novalue": "annassign.no-value",
    "ann_lab::ann_novalue_read": "annassign.no-value",
    "ann_lab::ann_novalue_shadows_global": "annassign.no-value",
    "ann_lab::ann_attr_target": "annassign.non-simple-target",
    "assert_lab::msg_set": "set.order",
    "assert_lab::catch_assert": "exc.handler",
    "fstring_lab::conversion_repr": "fstring.conversion",
    "fstring_lab::conversion_ascii": "fstring.conversion",
    "fstring_lab::format_spec": "fstring.format-spec",
    "fstring_lab::format_spec_num": "fstring.format-spec",
    "fstring_lab::debug_spec": "fstring.conversion",
    "fstring_lab::set_field": "set.order",
    "fstring_shadow::shadowed": "shadow.module-census",
    "fstring_shadow::elsewhere": "shadow.module-census",
    "alias_lab::read_alias": "firstclass.callable",
    "del_lab::read_after": "del.name-set-census",
    "del_lab::rebind_after": "del.name-set-census",
    "del_lab::loop_del": "del.name-set-census",
    "del_lab::del_global": "del.name-set-census",
    "del_lab::del_never": "del.name-set-census",
    "del_lab::double_del": "del.name-set-census",
    "del_lab::del_sub": "del.non-name-target",
    "del_lab::del_attr": "del.non-name-target",
}

# The two-model window is CLOSED. `MONO_OPENED` listed rows the trunk refused
# and the rebuild answered, and it explicitly refused to adjudicate them --
# `harness/monadic_gate.py` did, by checking the rebuild against the ORACLE.
# That gate is deleted with the window, so leaving the table would turn it
# into exactly the silencer its own comment disclaimed. Instead the two rows
# were migrated in `harness/cases.json` from `expect: unsupported` to
# `expect: match`: they leave the whitelist entirely and CPython adjudicates
# them as ordinary differential rows. Records-vs-adjudicates is preserved --
# the adjudicator is just diff_test now.

SCRIPT_CLASS = {
    "call_before_def": "script.definition-order",
    "cls_effect_script": "class.creation-effect",
    "prefix_forward": "script.definition-order",
    "print_set": "set.order",
    "print_nonascii": "str.non-ascii",
    "import_not_top_level": "import.position",
    "alias_before_def": "alias.admission",
    "ann_module_script": "annassign.module-scope",
    "alias_rebound": "alias.admission",
    "del_def_mid_script": "del.definition-name",
    "del_dunder_script": "del.definition-name",
    "del_import_script": "del.definition-name",
    "fmt_width_script": "format.percent-minilanguage",
    "cls_deco_script": "class.creation-effect",
    "star_target_script": "starred.position",
}


# ---------------------------------------------------------------------------
# Running
# ---------------------------------------------------------------------------

def run_batch(runner_cmd, lines, flag):
    """One runner process for the whole list; returns the parsed result
    lines in order. `flag` is `--batch` or `--script-batch`."""
    fd, jobs_path = tempfile.mkstemp(
        dir=os.path.join(REPO_ROOT, "harness"),
        prefix=".census_jobs.", suffix=".jsonl")
    with os.fdopen(fd, "w", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")
    out = []
    try:
        proc = subprocess.Popen(list(runner_cmd) + [flag, jobs_path],
                                cwd=REPO_ROOT, stdout=subprocess.PIPE,
                                text=True)
        for line in proc.stdout:
            line = line.strip()
            if not line:
                continue
            if not line.startswith("{"):
                print("runner: %s" % line, file=sys.stderr)
                continue
            out.append(json.loads(line))
        proc.wait()
    finally:
        os.unlink(jobs_path)
    while len(out) < len(lines):
        out.append({"status": "runner-error",
                    "msg": "runner produced %d of %d results"
                           % (len(out), len(lines))})
    return out


def oracle_run(path):
    proc = subprocess.run([ORACLE, path], cwd=REPO_ROOT,
                          capture_output=True, text=True)
    return proc.stdout, proc.returncode, proc.stderr


def verdict_of(cpy, model):
    """The verdict, in `harness/leanpy_survey.py`'s vocabulary and by its
    rule: stdout and exit code must agree, and an `exn` outcome must agree
    on the exception CLASS as well (CPython exits 1 for every uncaught
    exception, so stdout + exit alone cannot tell two apart)."""
    cout, ccode, cerr = cpy
    status = model.get("status")
    if status == "unsupported":
        return "REFUSE", model.get("msg", "")
    if status == "timeout":
        return "TIMEOUT", ""
    if status == "runner-error":
        return "ERROR", model.get("msg", "")
    if status == "exn" and cpython_exc_class(cerr) != model.get("exn"):
        return "DIVERGE", ("model raised %s | cpython raised %s"
                           % (model.get("exn"), cpython_exc_class(cerr)))
    lout, lcode = lean_stdout(model), model.get("exit")
    if cout == lout and ccode == lcode:
        return "MATCH", ""
    return "DIVERGE", ("model exit %s stdout %r | cpython exit %d stdout %r"
                       % (lcode, lout, ccode, cout))


def grammar_census(runner_cmd, keep, results):
    work = keep or tempfile.mkdtemp(prefix="census-witnesses-")
    os.makedirs(work, exist_ok=True)
    cache = leanpy.default_cache()
    os.makedirs(cache, exist_ok=True)
    paths, jobs, live = [], [], []
    for item in W:
        p = os.path.join(work, item["id"].replace(".", "-") + ".py")
        with open(p, "w", encoding="utf-8") as f:
            f.write(item["src"])
        env = leanpy.envelope_for(p, cache)
        if env is None:
            results.append((item["id"], "EXTRACT", "", item[EXPECT_KEY]))
            continue
        paths.append(p)
        jobs.append(json.dumps({"path": env}, separators=(",", ":")))
        live.append(item)
    models = run_batch(runner_cmd, jobs, "--script-batch")
    drift = 0
    for item, path, model in zip(live, paths, models):
        got, detail = verdict_of(oracle_run(path), model)
        results.append((item["id"], got, detail, item[EXPECT_KEY]))
        if got != item[EXPECT_KEY]:
            drift += 1
    return drift, work


def print_grammar(results):
    width = max(len(r[0]) for r in results)
    print("=" * 72)
    print("GRAMMAR CENSUS — one witness per CPython 3.9 `ast` production")
    print("=" * 72)
    for wid, got, detail, expect in results:
        flag = "" if got == expect else "   <<< DRIFT (recorded %s)" % expect
        print("%-*s  %-8s %s%s" % (width, wid, got, detail[:100], flag))
    live = sum(1 for r in results if r[1] == "MATCH")
    print("-" * 72)
    print("%d productions: %d MATCH, %d REFUSE, %d other"
          % (len(results), live,
             sum(1 for r in results if r[1] == "REFUSE"),
             sum(1 for r in results if r[1] not in ("MATCH", "REFUSE"))))


def bucket(rows):
    """rows: (class, key, message) -> ordered class table."""
    out = {}
    for cls, key, msg in rows:
        e = out.setdefault(cls, {"n": 0, "rep": key, "msgs": set()})
        e["n"] += 1
        if msg:
            e["msgs"].add(msg)
    return out


def print_buckets(title, table, total):
    print("=" * 72)
    print(title)
    print("=" * 72)
    width = max([len(c) for c in table] + [5])
    for cls in sorted(table, key=lambda c: (-table[c]["n"], c)):
        e = table[cls]
        msg = sorted(e["msgs"])[0] if e["msgs"] else "(no message)"
        print("%-*s  %3d  %-28s %s" % (width, cls, e["n"], e["rep"], msg[:70]))
    print("-" * 72)
    print("%d rows in %d classes" % (total, len(table)))


def whitelist_census(runner_cmd):
    with open(os.path.join(REPO_ROOT, "harness", "cases.json"),
              encoding="utf-8") as f:
        cases = json.load(f)
    jobs, keys = [], []
    unclassified = []
    for case in cases:
        if case.get("expect") != "unsupported":
            continue
        stem = os.path.splitext(os.path.basename(case["file"]))[0]
        key = "%s::%s" % (stem, case["function"])
        if key not in WHITELIST_CLASS:
            unclassified.append(key)
            continue
        env = os.path.splitext(case["file"])[0] + ".json"
        for args in case["args"]:
            job = {"path": env, "function": case["function"], "args": args}
            if case.get("fuel"):
                job["fuel"] = case["fuel"]
            jobs.append(json.dumps(job, separators=(",", ":")))
            keys.append(key)
    models = run_batch(runner_cmd, jobs, "--batch")
    rows = []
    not_refused = []
    for key, model in zip(keys, models):
        if model.get("status") != "unsupported":
            not_refused.append((key, model.get("status")))
        rows.append((WHITELIST_CLASS[key], key, model.get("msg", "")))
    print_buckets("WHITELIST CENSUS — harness/cases.json "
                  "`expect: unsupported` rows", bucket(rows), len(rows))
    drift = 0
    for key in unclassified:
        print("DRIFT: whitelisted row %s has no class in WHITELIST_CLASS"
              % key)
        drift += 1
    for key, status in not_refused:
        print("DRIFT: %s is whitelisted but the model answered %s"
              % (key, status))
        drift += 1
    return drift


def scripts_census(runner_cmd):
    with open(os.path.join(REPO_ROOT, "harness", "scripts.json"),
              encoding="utf-8") as f:
        script_rows = json.load(f)
    cache = leanpy.default_cache()
    jobs, keys = [], []
    drift = 0
    for row in script_rows:
        if row.get("expect") != "unsupported":
            continue
        stem = os.path.splitext(os.path.basename(row["file"]))[0]
        if stem not in SCRIPT_CLASS:
            print("DRIFT: loud script %s has no class in SCRIPT_CLASS" % stem)
            drift += 1
            continue
        env = leanpy.envelope_for(row["file"], cache)
        jobs.append(json.dumps({"path": env}, separators=(",", ":")))
        keys.append(stem)
    models = run_batch(runner_cmd, jobs, "--script-batch")
    rows = []
    for key, model in zip(keys, models):
        if model.get("status") != "unsupported":
            print("DRIFT: %s is a loud row but the model answered %s"
                  % (key, model.get("status")))
            drift += 1
        rows.append((SCRIPT_CLASS[key], key, model.get("msg", "")))
    print_buckets("SCRIPT CENSUS — harness/scripts.json "
                  "`expect: unsupported` rows", bucket(rows), len(rows))
    return drift


def main(argv=None):
    p = argparse.ArgumentParser(prog="refusal_census.py")
    p.add_argument("--grammar", action="store_true")
    p.add_argument("--whitelist", action="store_true")
    p.add_argument("--scripts", action="store_true")
    p.add_argument("--no-build", action="store_true")
    p.add_argument("--runner", default="lake exe leanmodels-run")
    p.add_argument("--json", default=None)
    p.add_argument("--keep", default=None,
                   help="write the grammar witnesses here and keep them")
    opts = p.parse_args(argv)
    if not (opts.grammar or opts.whitelist or opts.scripts):
        opts.grammar = opts.whitelist = opts.scripts = True

    os.chdir(REPO_ROOT)
    runner_cmd = opts.runner.split()
    print("interpreter: LeanModels/Python/Monadic/ (the only one)")
    # THE AMENDMENT 14 CONTRACT (tools/triad.sh 4d32526): the TENURE builds the
    # runner and exports LS_RUNNER_PREBUILT=1. A gate must never build the tree
    # — it defeats --build-target narrowing and surfaces an unrelated build
    # failure as a GATE failure, attributing the number to the wrong thing
    # (§5.4a). Unset, build ONLY the runner.
    if not opts.no_build and not os.environ.get("LS_RUNNER_PREBUILT"):
        if subprocess.run(["lake", "build", "leanmodels-run"], cwd=REPO_ROOT).returncode != 0:
            print("error: `lake build` failed", file=sys.stderr)
            return 2

    drift = 0
    grammar = []
    if opts.grammar:
        d, work = grammar_census(runner_cmd, opts.keep, grammar)
        drift += d
        print_grammar(grammar)
        if opts.keep:
            print("witnesses kept in %s" % work)
    if opts.whitelist:
        drift += whitelist_census(runner_cmd)
    if opts.scripts:
        drift += scripts_census(runner_cmd)

    ver = subprocess.run([ORACLE, "-V"], capture_output=True, text=True)
    print("oracle: %s" % ((ver.stdout or ver.stderr).strip(),))
    if opts.json:
        with open(opts.json, "w", encoding="utf-8") as f:
            json.dump({"grammar": [{"id": a, "verdict": b, "detail": c,
                                    "recorded": d} for a, b, c, d in grammar]},
                      f, indent=1)
    print("%d drift%s" % (drift, "" if drift == 1 else "s"))
    return 1 if drift else 0


if __name__ == "__main__":
    sys.exit(main())
