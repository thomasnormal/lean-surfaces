#!/usr/bin/env python3
"""class_census.py — what the CLASS-CREATION wall is actually made of.

    python3 harness/class_census.py [--cpython python3.9] [--json OUT]
                                    [--library] [--top N]
    python3 harness/class_census.py --controls

THE QUESTION. `classesCreationPure` is `runScript`'s FIRST admission
check, so every stdlib file holding one creation-impure class refuses
THERE, whatever else is wrong with it — which is why the dynamic
first-wall telemetry reads `class-creation 106` after the `%` landing.
That number says how many files hit the wall, and nothing whatever about
which BRICKS it is made of. This instrument reads the bricks: per class,
the base form, the class-body statement kinds, the metaclass/decorator
flags; per file, the minimal admissible TIER that would clear its class
wall, and whether clearing it would actually flip the file or merely
uncover the next wall.

THE RULES ARE PRE-REGISTERED in docs/memory-model.md §the class tier,
committed with this file and BEFORE any number below was quoted.

GROUND TRUTH, never a re-implementation: the wall predicate is the
extractor's own `creation_effects`, obtained by importing
`extractors/python/extract.py` and converting each top-level statement —
the same field `leanpy_survey.census` reads out of an envelope and the
same one `Json.lean`'s `parseClassDefn` re-checks. Only the CENSUS
DIMENSIONS (base form, body statement kinds, the feature demands) are
this file's own analysis, and every one of them is cross-checked against
that ground truth on every real file: a class may demand a feature only
if the extractor called it impure, modulo the three RECORDED exemptions
(a decorated METHOD, an `Exception` base, a `namedtuple(...)` base) —
each of which is a finding in its own right, printed by name.

TOP-LEVEL ONLY, because the wall is. `Module.classes` is filled from
top-level `ClassDef` nodes (Json.lean `parseModule`), so a class nested
in a function or in another class cannot make `classesCreationPure`
false; it refuses later, as an ordinary statement. The static wall
census in `leanpy_survey.py` walks the whole envelope and does count
them — the difference is reported, not smoothed over.

THE GATE: `--controls` runs 17 synthetic fixtures with hand-computed
verdicts plus two real-file controls, and main() runs them before the
census and aborts if any row fails. A classifier whose output was not
paid for with a positive and a negative control has burned this project
five times.

Python 3.9 compatible.
"""

import argparse
import ast
import collections
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import import_closure as ic
import leanpy_survey

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(REPO_ROOT, "extractors", "python"))
import extract  # noqa: E402  (the ground truth, imported not re-implemented)

sys.setrecursionlimit(20000)

# CPython 3.9's builtin exception names — a base drawn from here is an
# exception base even when it is not literally `Exception` (the extractor
# admits only the literal name, so `class E(ValueError)` is a wall today).
import builtins  # noqa: E402

EXC_NAMES = frozenset(n for n in dir(builtins)
                      if isinstance(getattr(builtins, n), type)
                      and issubclass(getattr(builtins, n), BaseException))
BUILTIN_TYPES = frozenset(n for n in dir(builtins)
                          if isinstance(getattr(builtins, n), type))

# The three RECORDED exemptions — forms this census counts as a demand
# although the extractor's `creation_effects` calls the class pure — are
# applied per class by `unexplained()` below, using the extractor's OWN
# structural recognition rather than the feature name: a recognized
# `Exception` base, a recognized `namedtuple` base, and a decorated method
# (THE THIRD DOOR — docs/memory-model.md §the class tier). Everything else
# must line up with the ground truth or the census aborts.


# ---------------------------------------------------------------------------
# per-class analysis
# ---------------------------------------------------------------------------

def _base_feature(b, class_names, import_names):
    """The FEATURE one base expression demands, as a string."""
    if isinstance(b, ast.Name):
        if b.id == "object":
            return "base:object"
        if b.id in class_names:
            return "base:same-module-class"
        if b.id in EXC_NAMES:
            return "base:exception"
        if b.id in BUILTIN_TYPES:
            return "base:builtin-type"
        if b.id in import_names:
            return "base:imported-name"
        return "base:other-name"
    if isinstance(b, ast.Attribute):
        return "base:dotted"
    if isinstance(b, ast.Call):
        if isinstance(b.func, ast.Name) and b.func.id == "namedtuple":
            return "base:namedtuple-call"
        return "base:call"
    if isinstance(b, ast.Subscript):
        return "base:subscript"
    return "base:other-expr"


def _rhs_shape(v):
    """A coarse, PRE-REGISTERED bucket for an assignment's right-hand side."""
    if isinstance(v, ast.Constant):
        return "literal"
    if isinstance(v, (ast.Tuple, ast.List, ast.Dict, ast.Set)):
        return "display"
    if isinstance(v, ast.Name):
        return "name"
    if isinstance(v, ast.Call):
        return "call"
    if isinstance(v, ast.Lambda):
        return "lambda"
    if isinstance(v, (ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp)):
        return "comprehension"
    if isinstance(v, (ast.BinOp, ast.UnaryOp, ast.BoolOp, ast.Compare, ast.IfExp)):
        return "operator"
    if isinstance(v, ast.Attribute):
        return "attribute"
    if isinstance(v, ast.Subscript):
        return "subscript"
    if isinstance(v, ast.JoinedStr):
        return "fstring"
    return "other"


def _body_features(node):
    """(feature set, statement-kind counter) for one class body."""
    feats = set()
    kinds = collections.Counter()
    for i, s in enumerate(node.body):
        if isinstance(s, ast.FunctionDef):
            if s.decorator_list:
                feats.add("body:decorated-def")
                kinds["def-decorated"] += 1
                for d in s.decorator_list:
                    nm = (d.id if isinstance(d, ast.Name)
                          else d.attr if isinstance(d, ast.Attribute)
                          else d.func.id if isinstance(d, ast.Call)
                          and isinstance(d.func, ast.Name) else "<expr>")
                    kinds["deco=" + nm] += 1
            else:
                kinds["def"] += 1
            continue
        if isinstance(s, ast.AsyncFunctionDef):
            feats.add("body:async-def")
            kinds["async-def"] += 1
            continue
        if isinstance(s, ast.Pass):
            kinds["pass"] += 1
            continue
        if isinstance(s, ast.Expr) and isinstance(s.value, ast.Constant):
            kinds["docstring" if i == 0 else "const-expr"] += 1
            continue
        if isinstance(s, ast.Expr):
            feats.add("body:expr-stmt")
            kinds["expr-stmt"] += 1
            continue
        if isinstance(s, ast.Assign):
            plain = all(isinstance(t, ast.Name) for t in s.targets)
            shape = _rhs_shape(s.value)
            names = [t.id for t in s.targets if isinstance(t, ast.Name)]
            if not plain:
                feats.add("body:complex-target")
                kinds["assign-complex-target"] += 1
                continue
            if "__slots__" in names:
                feats.add("body:slots")
                kinds["slots"] += 1
                continue
            if any(n.startswith("__") and n.endswith("__") for n in names):
                # `__hash__ = None`, `__eq__ = _eq`, … — a namespace binding
                # that changes the object PROTOCOL, so it is never "just an
                # attribute" and never rides the ordinary assign arm.
                feats.add("body:dunder-assign")
                kinds["dunder-assign"] += 1
                continue
            if shape == "literal":
                kinds["assign-literal"] += 1        # already in tier
                continue
            feats.add("body:assign-" + shape)
            kinds["assign-" + shape] += 1
            continue
        if isinstance(s, ast.AnnAssign):
            feats.add("body:annassign")
            kinds["annassign"] += 1
            continue
        if isinstance(s, ast.AugAssign):
            feats.add("body:augassign")
            kinds["augassign"] += 1
            continue
        if isinstance(s, (ast.If, ast.For, ast.While, ast.Try, ast.With,
                          ast.AsyncFor, ast.AsyncWith)):
            feats.add("body:control")
            kinds["control:" + type(s).__name__] += 1
            continue
        if isinstance(s, ast.ClassDef):
            feats.add("body:nested-class")
            kinds["nested-class"] += 1
            continue
        if isinstance(s, (ast.Import, ast.ImportFrom)):
            feats.add("body:import")
            kinds["import"] += 1
            continue
        if isinstance(s, ast.Delete):
            feats.add("body:del")
            kinds["del"] += 1
            continue
        if isinstance(s, ast.Global):
            feats.add("body:global")
            kinds["global"] += 1
            continue
        if isinstance(s, ast.Nonlocal):
            feats.add("body:nonlocal")
            kinds["nonlocal"] += 1
            continue
        if isinstance(s, ast.Raise):
            feats.add("body:raise")
            kinds["raise"] += 1
            continue
        if isinstance(s, ast.Assert):
            feats.add("body:assert")
            kinds["assert"] += 1
            continue
        feats.add("body:other:" + type(s).__name__)
        kinds["other:" + type(s).__name__] += 1
    return feats, kinds


def class_row(node, class_names, import_names, truth, recognized=None):
    """One top-level class: its demands, its shape, the extractor's verdict.

    ``recognized`` is the extractor's own structural recognition of the base
    (``"exc"`` for the exact `class N(Exception): pass` shape, ``"nt"`` for a
    plain `namedtuple(...)` base, ``None`` otherwise) — it is what makes the
    ground-truth cross-check exact instead of exempting a whole feature.
    """
    feats, kinds = _body_features(node)
    bases = [_base_feature(b, class_names, import_names) for b in node.bases]
    if len(node.bases) > 1:
        feats.add("base:multiple")
    feats.update(bases)
    if node.keywords:
        feats.add("meta:keywords")
    if node.decorator_list:
        feats.add("meta:decorators")
    dunders = sorted(s.name for s in node.body
                     if isinstance(s, (ast.FunctionDef, ast.AsyncFunctionDef))
                     and s.name.startswith("__") and s.name.endswith("__")
                     and s.name != "__init__")
    return {
        "name": node.name,
        "line": node.lineno,
        "nbases": len(node.bases),
        "bases": bases,
        "keywords": bool(node.keywords),
        "decorators": bool(node.decorator_list),
        "methods": sum(1 for s in node.body
                       if isinstance(s, (ast.FunctionDef, ast.AsyncFunctionDef))),
        "dunders_beyond_init": dunders,
        "kinds": dict(kinds),
        "demands": sorted(feats),
        "creation_effects": truth,
        "recognized": recognized,
    }


def unexplained(c):
    """The demands NOT accounted for by the extractor's own recognition.

    `demands ≠ ∅ ⟺ creation_effects` must hold once these are removed — that
    is the cross-check, and each survivor is a recorded finding, not noise.
    """
    ex = set()
    if c.get("recognized") == "exc":
        ex.add("base:exception")
    if c.get("recognized") == "nt":
        ex.add("base:namedtuple-call")
    ex.add("body:decorated-def")          # THE HOLE — a demand that is no effect
    return [d for d in c["demands"] if d not in ex]


# ---------------------------------------------------------------------------
# per-file analysis
# ---------------------------------------------------------------------------

def _import_names(tree):
    out = set()
    for s in ast.walk(tree):
        if isinstance(s, ast.Import):
            for a in s.names:
                out.add(a.asname or a.name.split(".")[0])
        elif isinstance(s, ast.ImportFrom):
            for a in s.names:
                out.add(a.asname or a.name)
    return out


def _module_envelope(tree):
    """The extractor's own module dict — GROUND TRUTH, built in memory."""
    return {"kind": "Module",
            "body": [extract.convert_stmt(s, module_scope=True) for s in tree.body]}


def _walls_of(env_module):
    """`leanpy_survey.census`'s wall set, over an in-memory module dict."""
    total, kinds, walls = 0, [], set()
    stack = [env_module]
    while stack:
        node = stack.pop()
        if isinstance(node, dict):
            if "kind" in node:
                total += 1
                k = node["kind"]
                if k == "Unsupported":
                    py = node.get("py_kind", "?")
                    kinds.append(py)
                    if py in ("Import", "ImportFrom"):
                        if node.get("text", "") not in leanpy_survey.BENIGN_IMPORTS:
                            walls.add("import")
                    else:
                        walls.add("node:" + py)
                elif k == "ClassDef" and node.get("creation_effects"):
                    walls.add("class-creation")
            stack.extend(node.values())
        elif isinstance(node, list):
            stack.extend(node)
    return sorted(walls)


def file_row(path, name):
    try:
        with open(path, "r", encoding="utf-8", errors="surrogateescape") as f:
            src = f.read()
        tree = ast.parse(src)
    except Exception as e:                       # noqa: BLE001 — reported, not hidden
        return {"module": name, "file": path, "error": "parse: %s" % e}
    try:
        env = _module_envelope(tree)
    except Exception as e:                       # noqa: BLE001
        return {"module": name, "file": path, "error": "extract: %s" % e}

    top = [s for s in tree.body if isinstance(s, ast.ClassDef)]
    class_names = set(s.name for s in top)
    imports = _import_names(tree)
    truth = {}
    for d in env["body"]:
        if d.get("kind") == "ClassDef":
            rec = ("nt" if d.get("namedtuple_base") is not None
                   else "exc" if d.get("exception_base") else None)
            truth[(d["name"], d["span"]["lineno"])] = (
                bool(d.get("creation_effects")), rec)

    rows = []
    for node in top:
        t = truth.get((node.name, node.lineno))
        if t is None:                            # the extractor refused the node
            rows.append({"name": node.name, "line": node.lineno,
                         "demands": ["extractor:not-a-classdef"],
                         "creation_effects": True, "bases": [], "nbases": 0,
                         "keywords": False, "decorators": False, "methods": 0,
                         "dunders_beyond_init": [], "kinds": {},
                         "recognized": None})
            continue
        rows.append(class_row(node, class_names, imports, t[0], t[1]))

    walls = _walls_of(env)
    demands = sorted(set(d for r in rows for d in r["demands"]))
    # module-level USE of a class name, outside every class body
    used, built = set(), set()
    for s in tree.body:
        if isinstance(s, ast.ClassDef):
            continue
        for n in ast.walk(s):
            if isinstance(n, ast.Name) and n.id in class_names:
                used.add(n.id)
            if (isinstance(n, ast.Call) and isinstance(n.func, ast.Name)
                    and n.func.id in class_names):
                built.add(n.func.id)
    nested = sum(1 for n in ast.walk(tree)
                 if isinstance(n, ast.ClassDef) and n not in top)
    return {
        "module": name, "file": path,
        "classes": rows,
        "nclasses": len(rows),
        "nimpure": sum(1 for r in rows if r["creation_effects"]),
        "nested_classes": nested,
        "walls": walls,
        "class_walled": any(r["creation_effects"] for r in rows),
        "demands": demands,
        "other_walls": [w for w in walls if w != "class-creation"],
        "used_at_module_level": sorted(used),
        "built_at_module_level": sorted(built),
        "defines_only": len(class_names) > 0 and not used,
    }


# ---------------------------------------------------------------------------
# the tier ladder (PRE-REGISTERED — docs/memory-model.md §the class tier)
# ---------------------------------------------------------------------------

# The assignment RHS shapes v0 admits: ORDINARY expressions, evaluated in
# the class frame. A comprehension or a lambda is a NESTED SCOPE — CPython's
# class scope is not a closure scope, so those are loud, not cheap.
ASSIGN_FEATS = frozenset(
    ["body:assign-name", "body:assign-call", "body:assign-display",
     "body:assign-operator", "body:assign-attribute", "body:assign-subscript",
     "body:assign-fstring", "body:assign-other", "body:expr-stmt"])

TIERS = [
    ("T0  today — a pure creation is SKIPPED, nothing executes", frozenset()),
    ("T1  the body EXECUTES: computed attributes, no base", ASSIGN_FEATS),
    ("T2  + an explicit `object` base", frozenset(["base:object"])),
    ("T3  + ONE base, a same-module class  <<< v0 BOUNDARY",
     frozenset(["base:same-module-class"])),
    ("T4  + ONE base, a builtin EXCEPTION  <<< v0 BOUNDARY",
     frozenset(["base:exception"])),
    ("T5  + `__slots__` (the storage rule, priced separately)",
     frozenset(["body:slots"])),
    ("T6  + decorated METHODS (the descriptor protocol)",
     frozenset(["body:decorated-def"])),
    ("T7  + a base that is an IMPORTED or dotted name (needs a module system)",
     frozenset(["base:imported-name", "base:dotted"])),
    ("T8  + a builtin-TYPE base (dict/list/str/…)",
     frozenset(["base:builtin-type", "base:other-name"])),
    ("T9  + MULTIPLE inheritance (a real MRO)", frozenset(["base:multiple"])),
    ("T10 + metaclass=, class decorators, dunder bindings",
     frozenset(["meta:keywords", "meta:decorators", "body:dunder-assign"])),
    ("T11 + everything else (body control flow, nested scopes, async, …)",
     None),
]

# The v0 boundary as a NAMED set, so the memo and the instrument cannot
# drift apart: T1+T2+T3+T4 of the ladder.
V0 = frozenset(ASSIGN_FEATS
               | {"base:object", "base:same-module-class", "base:exception"})


def tier_sets():
    """Cumulative admitted-feature sets, in ladder order. None = admit all."""
    out, acc = [], set()
    for label, add in TIERS:
        if add is None:
            out.append((label, None))
        else:
            acc = acc | add
            out.append((label, frozenset(acc)))
    return out


def clears(row, admitted):
    if admitted is None:
        return True
    return all(d in admitted for d in row["demands"])


def greedy(rows, limit=14):
    """[(feature, files newly cleared, running total)] — the honest curve.

    A file clears when EVERY demand of EVERY one of its classes is admitted,
    so the useful ranking is a set cover, not a frequency histogram: the
    feature at the top of the frequency list may clear nobody at all.
    """
    remaining = [set(r["demands"]) for r in rows if r["demands"]]
    provided, out, total = set(), [], 0
    for _ in range(limit):
        freq = collections.Counter()
        for d in remaining:
            for f in d - provided:
                freq[f] += 1
        if not freq:
            break
        best, gain = None, -1
        for f, _n in freq.most_common():
            g = sum(1 for d in remaining if d - provided - {f} == set())
            if g > gain:
                best, gain = f, g
        provided.add(best)
        newly = [d for d in remaining if d <= provided]
        remaining = [d for d in remaining if not (d <= provided)]
        total += len(newly)
        out.append((best, len(newly), total))
    return out


# ---------------------------------------------------------------------------
# controls — the gate
# ---------------------------------------------------------------------------

FIXTURES = [
    ("plain methods only", "class C:\n    def m(self): pass\n", [], False),
    ("literal attribute", "class C:\n    kind = 'tag'\n", [], False),
    ("docstring + pass", "class C:\n    'doc'\n    pass\n", [], False),
    ("computed attribute", "class C:\n    x = f()\n", ["body:assign-call"], True),
    ("name attribute", "class C:\n    x = y\n", ["body:assign-name"], True),
    ("__slots__", "class C:\n    __slots__ = ()\n", ["body:slots"], True),
    ("object base", "class C(object):\n    pass\n", ["base:object"], True),
    ("same-module base",
     "class A:\n    pass\nclass B(A):\n    pass\n", ["base:same-module-class"], True),
    ("Exception base", "class E(Exception):\n    pass\n", ["base:exception"], False),
    ("ValueError base", "class E(ValueError):\n    pass\n", ["base:exception"], True),
    ("multiple bases",
     "class A:\n    pass\nclass B:\n    pass\nclass C(A, B):\n    pass\n",
     ["base:multiple", "base:same-module-class"], True),
    ("metaclass", "class C(metaclass=M):\n    pass\n", ["meta:keywords"], True),
    ("class decorator", "@deco\nclass C:\n    pass\n", ["meta:decorators"], True),
    ("dotted base", "import a.b\nclass C(a.b.M):\n    pass\n", ["base:dotted"], True),
    ("namedtuple base",
     "from collections import namedtuple\n"
     "class P(namedtuple('P', 'x y')):\n    pass\n", ["base:namedtuple-call"], False),
    ("decorated method — THE HOLE",
     "class C:\n    @property\n    def x(self): return 1\n",
     ["body:decorated-def"], False),
    ("control flow in body",
     "class C:\n    if x:\n        y = 1\n", ["body:control"], True),
    ("nested class",
     "class C:\n    class D:\n        pass\n", ["body:nested-class"], True),
    ("bare call in body", "class C:\n    register()\n", ["body:expr-stmt"], True),
]


def controls(verbose=True):
    """Every fixture's demands and the extractor's verdict, hand-computed."""
    bad = 0
    for label, src, want, want_effects in FIXTURES:
        tree = ast.parse(src)
        top = [s for s in tree.body if isinstance(s, ast.ClassDef)]
        names = set(s.name for s in top)
        imports = _import_names(tree)
        env = _module_envelope(tree)
        truth = [(bool(d.get("creation_effects")),
                  "nt" if d.get("namedtuple_base") is not None
                  else "exc" if d.get("exception_base") else None)
                 for d in env["body"] if d.get("kind") == "ClassDef"]
        node = top[-1]
        got = class_row(node, names, imports, truth[-1][0], truth[-1][1])
        ok = (got["demands"] == sorted(want)
              and truth[-1][0] == want_effects
              # the cross-check the census runs on every real file, on the
              # fixtures too: unexplained demands ⟺ creation effects
              and bool(unexplained(got)) == want_effects)
        truth[-1] = truth[-1][0]
        bad += 0 if ok else 1
        if verbose or not ok:
            print("  %-4s %-34s demands=%-46s creation_effects=%s%s"
                  % ("ok" if ok else "FAIL", label, ",".join(got["demands"]) or "-",
                     truth[-1],
                     "" if ok else "  WANT demands=%s effects=%s"
                     % (",".join(sorted(want)) or "-", want_effects)))
    # real-file controls: a hand-read stdlib module must come out as read
    table = ic.ModuleTable.of(os.environ.get("LEANPY_CPYTHON") or "python3.9")
    for mod, want_walled, want_classes in (("graphlib", True, 3),
                                           ("opcode", False, 0),
                                           ("bisect", False, 0)):
        path = os.path.join(table.lib, mod + ".py")
        r = file_row(path, mod)
        ok = (r.get("class_walled") == want_walled
              and r.get("nclasses") == want_classes)
        bad += 0 if ok else 1
        print("  %-4s real file %-24s walled=%s classes=%s%s"
              % ("ok" if ok else "FAIL", mod, r.get("class_walled"),
                 r.get("nclasses"),
                 "" if ok else "  WANT walled=%s classes=%s" % (want_walled,
                                                                want_classes)))
    print("controls: %d fixture(s) + 3 real files, %d FAILED"
          % (len(FIXTURES), bad))
    return bad


# ---------------------------------------------------------------------------

def report(title, rows, top, discount=()):
    """``discount`` names walls another layer would resolve — for the LIBRARY
    population that is `import`, exactly as `import_closure.tier_census`
    discounts it: a module the module system imported has its import wall
    answered by construction, so counting it again would hide the tier's
    real reach."""
    walled = [r for r in rows if r.get("class_walled")]
    withcls = [r for r in rows if r.get("nclasses")]
    print("=" * 78)
    print("%s — %d files, %d define a top-level class, %d are CLASS-WALLED"
          % (title, len(rows), len(withcls), len(walled)))
    if not walled:
        return
    nclasses = sum(r["nclasses"] for r in walled)
    nimpure = sum(r["nimpure"] for r in walled)
    print("  %d top-level classes in them, %d creation-IMPURE (%.0f%%)"
          % (nclasses, nimpure, 100.0 * nimpure / nclasses))
    print("  class wall is the file's ONLY wall: %d"
          % sum(1 for r in walled if not r["other_walls"]))
    print("  files whose classes are never NAMED at module level: %d"
          % sum(1 for r in walled if r["defines_only"]))
    print("  files that INSTANTIATE one of their own classes at module "
          "level: %d" % sum(1 for r in walled if r["built_at_module_level"]))
    print("  files with a class nested in a function/class body too: %d"
          % sum(1 for r in walled if r["nested_classes"]))

    print("-" * 78)
    print("BASE FORMS — over the %d creation-impure classes" % nimpure)
    bf = collections.Counter()
    nb = collections.Counter()
    for r in walled:
        for c in r["classes"]:
            if not c["creation_effects"]:
                continue
            nb[c["nbases"] if c["nbases"] < 3 else "3+"] += 1
            for b in c["bases"]:
                bf[b] += 1
            if not c["bases"]:
                bf["(no base)"] += 1
    for k in sorted(nb, key=str):
        print("  %-24s %4d" % ("bases=%s" % k, nb[k]))
    for f, n in bf.most_common():
        print("  %-24s %4d" % (f, n))

    print("-" * 78)
    print("CLASS-BODY STATEMENT KINDS — over the same classes "
          "(classes containing at least one)")
    kk = collections.Counter()
    for r in walled:
        for c in r["classes"]:
            if not c["creation_effects"]:
                continue
            for k in c["kinds"]:
                kk[k] += 1
    for k, n in kk.most_common(top):
        print("  %-24s %4d" % (k, n))

    print("-" * 78)
    print("FEATURE DEMANDS — files demanding each (a file clears only when "
          "ALL are admitted)")
    df = collections.Counter()
    sole = collections.Counter()
    for r in walled:
        for d in r["demands"]:
            df[d] += 1
        if len(r["demands"]) == 1:
            sole[r["demands"][0]] += 1
    for f, n in df.most_common():
        print("  present %4d   sole %4d   %s" % (n, sole.get(f, 0), f))

    print("-" * 78)
    print("THE LADDER — cumulative tiers, PRE-REGISTERED before the run")
    lab = "FLIPS" if not discount else "FLIPS*"
    print("  %-58s %6s %6s" % ("", "clears", lab))
    for label, admitted in tier_sets():
        cleared = [r for r in walled if clears(r, admitted)]
        flips = [r for r in cleared
                 if not [w for w in r["other_walls"] if w not in discount]]
        print("  %-58s %6d %6d" % (label, len(cleared), len(flips)))
    if discount:
        print("  * FLIPS discounts %s — the wall the layer below answers"
              % ", ".join(discount))
    v0 = [r for r in walled if clears(r, V0)]
    print("  v0 CLEARS %d of %d class-walled files; what the OTHER %d still "
          "demand, ranked:" % (len(v0), len(walled), len(walled) - len(v0)))
    rest = collections.Counter()
    for r in walled:
        if r in v0:
            continue
        for d in r["demands"]:
            if d not in V0:
                rest[d] += 1
    for f, n in rest.most_common(10):
        print("      %-28s %4d" % (f, n))

    print("-" * 78)
    print("GREEDY COVER — the honest curve (set cover, not frequency)")
    for f, newly, tot in greedy(walled):
        print("  +%-40s clears %3d more, %3d/%d total"
              % (f, newly, tot, len(walled)))


def main(argv=None):
    p = argparse.ArgumentParser(prog="class_census.py")
    p.add_argument("paths", nargs="*", metavar="PATH_OR_GLOB")
    p.add_argument("--cpython", default=os.environ.get("LEANPY_CPYTHON")
                   or "python3.9")
    p.add_argument("--library", action="store_true",
                   help="also census the pure-Python modules reachable in the "
                        "seeds' IMPORT-TIME closures (the second population — "
                        "where class-creation is the top blocker)")
    p.add_argument("--top", type=int, default=24)
    p.add_argument("--json", dest="json_out", default=None)
    p.add_argument("--controls", action="store_true",
                   help="run the gate and stop")
    opts = p.parse_args(argv)

    print("controls (the gate — a classifier is worth its controls):")
    bad = controls(verbose=True)
    if bad:
        raise SystemExit("class_census: %d control(s) FAILED — census aborted" % bad)
    if opts.controls:
        return 0

    table = ic.ModuleTable.of(opts.cpython)
    print("reference: CPython %s at %s" % (table.version, table.lib))
    seeds = ic.expand(opts.paths) or ic.stdlib_seeds(table)
    seed_rows = [file_row(p_, os.path.basename(p_)[:-3]) for p_ in seeds]
    errs = [r for r in seed_rows if "error" in r]
    for r in errs:
        print("  ERROR %-24s %s" % (r["module"], r["error"]))
    seed_rows = [r for r in seed_rows if "error" not in r]

    # the cross-check against ground truth, on every real file
    viol = []
    for r in seed_rows:
        for c in r["classes"]:
            if bool(unexplained(c)) != bool(c["creation_effects"]):
                viol.append((r["module"], c["name"], c["demands"],
                             c["creation_effects"]))
    print("GROUND-TRUTH cross-check over %d top-level classes "
          "(unexplained demands ≠ ∅ ⟺ creation_effects): %d violation(s)"
          % (sum(r["nclasses"] for r in seed_rows), len(viol)))
    for m, c, d, e in viol[:20]:
        print("    %-20s %-28s demands=%s effects=%s" % (m, c, ",".join(d), e))
    # THE HOLE, counted: a class the extractor calls PURE that nonetheless
    # runs a decorator at the `class` statement (docs/memory-model.md
    # §the class tier, "the third door").
    hole = [(r["module"], c["name"]) for r in seed_rows for c in r["classes"]
            if not c["creation_effects"] and "body:decorated-def" in c["demands"]]
    holef = sorted(set(m for m, _ in hole))
    print("THE THIRD DOOR — creation-PURE classes running a decorator at the "
          "`class` statement: %d classes in %d files" % (len(hole), len(holef)))
    admitted = [m for m in holef
                if not [r for r in seed_rows if r["module"] == m][0]["class_walled"]]
    print("  of which in files the class admission ADMITS today (a live "
          "silent-divergence risk): %d — %s"
          % (len(admitted), ", ".join(admitted) or "none"))
    # reconciliation with the DYNAMIC first-wall count: ingestion DEMOTES a
    # recognized Exception/namedtuple candidate on a module census failure and
    # sets creationPure := false, so a statically-pure file can still wall.
    demo = [r["module"] for r in seed_rows if not r["class_walled"]
            and any(c.get("recognized") for c in r["classes"])]
    print("RECONCILIATION: statically class-pure files holding a recognized "
          "Exception/namedtuple candidate ingestion may DEMOTE: %d — %s"
          % (len(demo), ", ".join(demo) or "none"))

    report("SEEDS — the stdlib sweep", seed_rows, opts.top)

    lib_rows = []
    if opts.library:
        mods = {}
        for path in seeds:
            name = os.path.basename(path)[:-3]
            rec = ic.closure(table, path, name, "top")
            for m in rec["modules"]:
                if m == name or m in mods:
                    continue
                kind, mp = table.resolve(m)
                if kind == "pure" and mp:
                    mods[m] = mp
        lib_rows = [file_row(v, k) for k, v in sorted(mods.items())]
        lib_rows = [r for r in lib_rows if "error" not in r]
        report("LIBRARY — pure-Python modules in the import-time closures",
               lib_rows, opts.top, discount=("import",))

    if opts.json_out:
        with open(opts.json_out, "w", encoding="utf-8") as f:
            json.dump({"cpython": table.version, "lib": table.lib,
                       "seeds": seed_rows, "library": lib_rows}, f, indent=1)
        print("wrote %s" % opts.json_out)
    return 0


if __name__ == "__main__":
    sys.exit(main())
