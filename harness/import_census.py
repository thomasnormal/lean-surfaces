#!/usr/bin/env python3
"""import_census.py — the import-ceiling CENSUS over the sweep's refusing files.

    python3 harness/import_census.py --sweep SWEEP.json [--cpython python3.9]
                                     [--json OUT] [--top N]
    python3 harness/import_census.py --self-test
    python3 harness/import_census.py --controls

THE QUESTION, narrower than import_closure.py's. That tool measures the
import ceiling of every stdlib seed; this one measures it for exactly the
files the completeness sweep REFUSES on `import` — the set an import
implementation would be built FOR — and it splits the verdict one notch
finer, because the coarse split undersells the classic stdlib pattern

    try:
        from _heapq import *        # the C accelerator
    except ImportError:
        pass                        # the pure fallback

which import_closure.py counts as C-REACHING even though a Python-only
module system runs the fallback branch and never misses the accelerator.

THE RULES ARE PRE-REGISTERED in docs/import-ceiling-census.md, committed
BEFORE the census was run. In brief: every seed gets TWO closures —

  FULL     optional (try/except-ImportError-guarded) imports SUCCEED:
           try-body imports followed, handler fallbacks not
  STRICT   optional imports FAIL: try-body accelerator imports dropped,
           handler fallbacks followed

both at IMPORT-TIME scope (module body, def/class bodies excluded;
`if TYPE_CHECKING:` bodies excluded as runtime-false; the seed's own
`__main__` guard live, imported modules' guards dead) — and the verdict is

  C-BLOCKED    the STRICT closure reaches a C builtin or extension module:
               even with every accelerator absent, C runs
  PURE-ACCEL   STRICT closure pure, FULL reaches C only through optional
               accelerator branches: a Python-only module system runs it
  PURE         both closures pure
  UNRESOLVED   the STRICT closure names a module the pinned platform does
               not ship, unguarded — reported apart, NEVER folded into pure
  NO-IMPORT    nothing imported at import time (the file's `import` wall is
               inside a function body)

C DETECTION is by the pinned interpreter's own inventory, never by name
convention: `sys.builtin_module_names` plus the `.so`/`.pyd`/`.dylib`
stems of lib-dynload (import_closure.ModuleTable, asked via subprocess,
nothing imported).

THE GATE: main() runs the synthetic self-test AND the real-table controls
(a hand-verified pure module must say PURE, `math` and `_socket` must say
C-BLOCKED, a nonexistent module must say UNRESOLVED) before the census,
and aborts if any row fails. A classifier whose output was not paid for
with a positive and a negative control has burned this project five times.

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

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

BRANCHES = ("always", "acc", "fb")


# ---------------------------------------------------------------------------
# static imports, one file, import-time scope, branch-tagged
# ---------------------------------------------------------------------------

def _catches_importerror(handlers):
    """Would this try's handlers swallow a failed import?  ImportError and
    ModuleNotFoundError by name; bare `except:`, Exception, BaseException
    because they swallow it too (pre-registered tie-break)."""
    for h in handlers:
        if h.type is None:
            return True
        elts = h.type.elts if isinstance(h.type, ast.Tuple) else [h.type]
        for e in elts:
            nm = getattr(e, "id", None) or getattr(e, "attr", None)
            if nm in ("ImportError", "ModuleNotFoundError",
                      "Exception", "BaseException"):
                return True
    return False


def _is_type_checking(node):
    """`if TYPE_CHECKING:` / `if typing.TYPE_CHECKING:` — runtime-false."""
    if not isinstance(node, ast.If):
        return False
    t = node.test
    return ((isinstance(t, ast.Name) and t.id == "TYPE_CHECKING")
            or (isinstance(t, ast.Attribute) and t.attr == "TYPE_CHECKING"))


class FileFacts(object):
    def __init__(self):
        # name -> {"branches": set, "main": bool(AND), "maybe": bool(AND)}
        self.edges = {}
        self.dynamic = False        # __import__ / import_module seen
        self.typing_only = set()    # imported ONLY under `if TYPE_CHECKING:`
        self.forms = collections.Counter()  # plain / from / from-relative / star
        self.broken = False

    def record(self, name, branch, main, maybe):
        e = self.edges.setdefault(name, {"branches": set(),
                                         "main": True, "maybe": True})
        e["branches"].add(branch)
        e["main"] = e["main"] and main
        e["maybe"] = e["maybe"] and maybe

    def branch_of(self, name):
        """Collapse: imported unguarded anywhere, or on BOTH sides of an
        accelerator try, means it is imported no matter what — `always`."""
        b = self.edges[name]["branches"]
        if "always" in b or ("acc" in b and "fb" in b):
            return "always"
        return next(iter(b))

    def demands(self, mode, as_program):
        """[(name, maybe)] under FULL (accelerators succeed) or STRICT
        (accelerators fail) — the two pre-registered extremes."""
        live = ("always", "acc") if mode == "full" else ("always", "fb")
        out = []
        for name, e in sorted(self.edges.items()):
            if self.branch_of(name) not in live:
                continue
            if e["main"] and not as_program:
                continue
            out.append((name, e["maybe"]))
        return out


_MEMO = {}


def facts_of(path, modname):
    if (path, modname) not in _MEMO:
        _MEMO[(path, modname)] = _facts_of(path, modname)
    return _MEMO[(path, modname)]


def _facts_of(path, modname):
    ff = FileFacts()
    try:
        with open(path, "rb") as f:
            tree = ast.parse(f.read())
    except (SyntaxError, ValueError, OSError, UnicodeDecodeError):
        ff.broken = True
        return ff
    ispkg = os.path.basename(path) == "__init__.py"
    base = modname if ispkg else (modname.rsplit(".", 1)[0]
                                  if "." in modname else modname)

    def walk(node, branch, main):
        certain, mods = None, []
        if isinstance(node, ast.Import):
            certain = [m for a in node.names for m in ic._prefixes(a.name)]
            ff.forms["plain"] += 1
        elif isinstance(node, ast.ImportFrom):
            certain, mods = ic._from_targets(node, base)
            ff.forms["from-relative" if node.level else "from"] += 1
            if any(a.name == "*" for a in node.names):
                ff.forms["star"] += 1
        elif isinstance(node, ast.Call):
            nm = (getattr(node.func, "id", None)
                  or getattr(node.func, "attr", None))
            if nm in ("__import__", "import_module"):
                ff.dynamic = True
        if certain is not None:
            for m in certain:
                ff.record(m, branch, main, False)
            for m in mods:
                ff.record(m, branch, main, True)
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef, ast.Lambda)):
            # not import-time: only the DYNAMIC flag is still worth seeing
            for child in ast.walk(node):
                if isinstance(child, ast.Call):
                    nm = (getattr(child.func, "id", None)
                          or getattr(child.func, "attr", None))
                    if nm in ("__import__", "import_module"):
                        ff.dynamic = True
            return
        if _is_type_checking(node):
            for child in ast.walk(node):
                if isinstance(child, ast.Import):
                    for a in child.names:
                        ff.typing_only.add(a.name)
                elif isinstance(child, ast.ImportFrom):
                    c2, m2 = ic._from_targets(child, base)
                    ff.typing_only.update(c2[-1:])
            for child in node.orelse:
                walk(child, branch, main)
            return
        if not main and ic._is_main_guard(node):
            for child in node.body:
                walk(child, branch, True)
            for child in node.orelse:
                walk(child, branch, False)
            return
        if isinstance(node, ast.Try) and _catches_importerror(node.handlers):
            for child in node.body:
                walk(child, "acc" if branch == "always" else branch, main)
            for h in node.handlers:
                for child in h.body:
                    walk(child, "fb" if branch == "always" else branch, main)
            # else: runs only when the body raised nothing — accelerator side
            for child in node.orelse:
                walk(child, "acc" if branch == "always" else branch, main)
            for child in node.finalbody:
                walk(child, branch, main)
            return
        for child in ast.iter_child_nodes(node):
            walk(child, branch, main)

    for stmt in tree.body:
        walk(stmt, "always", False)
    # a name imported under TYPE_CHECKING *and* at runtime is a runtime import
    ff.typing_only -= set(n for n in ff.edges)
    return ff


# ---------------------------------------------------------------------------
# the two closures and the verdict
# ---------------------------------------------------------------------------

def one_closure(table, seed_path, seed_name, mode):
    """BFS from one seed under FULL or STRICT (queue, so depths are true)."""
    seen = {seed_name: 0}
    via, kinds = {}, {}
    dyn, broken, typing_only = set(), set(), set()
    frontier = collections.deque([(seed_name, seed_path, 0)])
    while frontier:
        name, path, depth = frontier.popleft()
        ff = facts_of(path, name)
        if ff.broken:
            broken.add(name)
            continue
        if ff.dynamic:
            dyn.add(name)
        typing_only.update(ff.typing_only)
        for m, maybe in ff.demands(mode, depth == 0):
            if m in seen:
                continue
            kind, p = table.resolve(m)
            if maybe and kind == "missing":
                continue        # `from p import x`: x is an attribute of p
            seen[m] = depth + 1
            via[m] = name
            kinds[m] = kind
            if kind == "pure":
                frontier.append((m, p, depth + 1))
    return {"modules": seen, "via": via, "kinds": kinds, "dynamic": sorted(dyn),
            "broken": sorted(broken), "typing_only": sorted(typing_only),
            "c": sorted(m for m, k in kinds.items()
                        if k in ("c-builtin", "c-ext")),
            "missing": sorted(m for m, k in kinds.items() if k == "missing")}


def classify(table, seed_path, seed_name):
    full = one_closure(table, seed_path, seed_name, "full")
    strict = one_closure(table, seed_path, seed_name, "strict")
    if len(full["modules"]) == 1 and len(strict["modules"]) == 1:
        verdict = "NO-IMPORT"
    elif strict["c"]:
        verdict = "C-BLOCKED"
    elif strict["missing"]:
        verdict = "UNRESOLVED"
    elif full["c"]:
        verdict = "PURE-ACCEL"
    else:
        verdict = "PURE"
    return {"module": seed_name, "file": seed_path, "verdict": verdict,
            "full": full, "strict": strict,
            # optional-missing: platform branches behind except ImportError —
            # counted and listed, never silently dropped, never a blocker
            "optional_missing": sorted(set(full["missing"])
                                       - set(strict["missing"]))}


def chain(cl, target):
    out = [target]
    while out[-1] in cl["via"]:
        out.append(cl["via"][out[-1]])
    return " -> ".join(reversed(out))


# ---------------------------------------------------------------------------
# controls — synthetic fixture AND the real table; the census will not run
# without them
# ---------------------------------------------------------------------------

FIXTURE = {
    "leaf.py":       "X = 1\n",
    "purely.py":     "import midway\n",
    "midway.py":     "import leaf\n",
    "direct_c.py":   "import _speedups\n",
    "deep_c.py":     "import viac\n",
    "viac.py":       "import _speedups\n",
    # the accelerator pattern, at the seed and one hop down
    "accel.py":      "try:\n    from _speedups import *\nexcept ImportError:\n    pass\n",
    "accel_fb.py":   "try:\n    import _speedups\nexcept ImportError:\n    import leaf\n",
    "via_accel.py":  "import accel\n",
    # the fallback itself needs C: no branch is pure
    "fb_c.py":       "try:\n    import _speedups\nexcept ImportError:\n    import viac\n",
    # missing: unguarded vs guarded
    "gone.py":       "import zzz_no_such_module\n",
    "gone_opt.py":   "try:\n    import zzz_no_such_module\nexcept ImportError:\n    import leaf\n",
    # runtime-false and not-at-import-time
    "typed.py":      "TYPE_CHECKING = False\nif TYPE_CHECKING:\n    import _speedups\nimport leaf\n",
    "lazy.py":       "def go():\n    import _speedups\n",
}

SELF_TEST = [
    ("purely",    "PURE",       [], []),
    ("leaf",      "NO-IMPORT",  [], []),
    ("direct_c",  "C-BLOCKED",  ["_speedups"], []),
    ("deep_c",    "C-BLOCKED",  ["_speedups"], []),
    ("accel",     "PURE-ACCEL", [], ["_speedups"]),
    ("accel_fb",  "PURE-ACCEL", [], ["_speedups"]),
    ("via_accel", "PURE-ACCEL", [], ["_speedups"]),
    ("fb_c",      "C-BLOCKED",  ["_speedups"], ["_speedups"]),
    ("gone",      "UNRESOLVED", [], []),
    ("gone_opt",  "PURE",       [], []),
    ("typed",     "PURE",       [], []),
    ("lazy",      "NO-IMPORT",  [], []),
]


def self_test():
    import shutil
    import tempfile
    root = tempfile.mkdtemp(prefix="import-census-selftest-")
    bad = 0
    try:
        for rel, src in FIXTURE.items():
            with open(os.path.join(root, rel), "w", encoding="utf-8") as f:
                f.write(src)
        table = ic.ModuleTable(root, ["_speedups"], [], "fixture")
        for seed, want_v, want_strict_c, want_full_c in SELF_TEST:
            r = classify(table, os.path.join(root, seed + ".py"), seed)
            ok = (r["verdict"] == want_v and r["strict"]["c"] == want_strict_c
                  and r["full"]["c"] == want_full_c)
            bad += 0 if ok else 1
            print("  %-4s %-10s want %-10s strictC=%-10s got %-10s strictC=%s"
                  % ("ok" if ok else "FAIL", seed, want_v,
                     ",".join(want_strict_c) or "-", r["verdict"],
                     ",".join(r["strict"]["c"]) or "-"))
        # gone_opt must REPORT its optional-missing, not swallow it
        r = classify(table, os.path.join(root, "gone_opt.py"), "gone_opt")
        ok = r["optional_missing"] == ["zzz_no_such_module"]
        bad += 0 if ok else 1
        print("  %-4s gone_opt   optional-missing reported: %s"
              % ("ok" if ok else "FAIL", r["optional_missing"]))
    finally:
        shutil.rmtree(root, ignore_errors=True)
    print("SELF-TEST: %d of %d rows failed" % (bad, len(SELF_TEST) + 1))
    return bad


# real-table controls: (source text, expected verdict) — `keyword` is the
# hand-verified pure module (zero import statements in 3.9.19's keyword.py);
# math/_socket are the mandated negative controls; the last is the mandated
# unresolvable, which must be UNRESOLVED and never silently pure.
REAL_CONTROLS = [
    ("import keyword\n",           "PURE"),
    ("import math\n",              "C-BLOCKED"),
    ("import _socket\n",           "C-BLOCKED"),
    ("import zzz_no_such_module\n", "UNRESOLVED"),
]


def real_controls(table):
    import shutil
    import tempfile
    root = tempfile.mkdtemp(prefix="import-census-controls-")
    bad = 0
    try:
        for i, (src, want) in enumerate(REAL_CONTROLS):
            path = os.path.join(root, "control_%d.py" % i)
            with open(path, "w", encoding="utf-8") as f:
                f.write(src)
            r = classify(table, path, "control_%d" % i)
            ok = r["verdict"] == want
            bad += 0 if ok else 1
            print("  %-4s %-28s want %-10s got %-10s strictC=%s missing=%s"
                  % ("ok" if ok else "FAIL", src.strip(), want, r["verdict"],
                     ",".join(r["strict"]["c"]) or "-",
                     ",".join(r["strict"]["missing"]) or "-"))
    finally:
        shutil.rmtree(root, ignore_errors=True)
    print("REAL-TABLE CONTROLS: %d of %d rows failed" % (bad, len(REAL_CONTROLS)))
    return bad


# ---------------------------------------------------------------------------

def import_forms(table, row):
    """Which import FORMS the seed's FULL closure actually uses, at
    import-time scope — the scoping data for an eventual implementation."""
    total = collections.Counter()
    for m in row["full"]["modules"]:
        kind, p = (("pure", row["file"]) if m == row["module"]
                   else table.resolve(m))
        if kind == "pure":
            total.update(facts_of(p, m).forms)
    return dict(total)


def main(argv=None):
    p = argparse.ArgumentParser(prog="import_census.py")
    p.add_argument("--sweep", default=None,
                   help="leanpy_survey --json output; seeds are its REFUSE "
                   "rows whose wall set contains `import`")
    p.add_argument("--cpython", default=os.environ.get("LEANPY_CPYTHON")
                   or "python3.9")
    p.add_argument("--self-test", dest="self_test", action="store_true")
    p.add_argument("--controls", action="store_true")
    p.add_argument("--top", type=int, default=15)
    p.add_argument("--json", dest="json_out", default=None)
    opts = p.parse_args(argv)

    if opts.self_test:
        return 1 if self_test() else 0
    if opts.controls:
        return 1 if real_controls(ic.ModuleTable.of(opts.cpython)) else 0
    if not opts.sweep:
        raise SystemExit("import_census: --sweep SWEEP.json is required "
                         "(or --self-test / --controls)")

    table = ic.ModuleTable.of(opts.cpython)
    print("reference: CPython %s at %s" % (table.version, table.lib))
    print("%d builtin modules, %d extension modules in lib-dynload"
          % (len(table.builtins), len(table.dynload)))

    # THE GATE: no census without green controls, synthetic and real.
    print("-" * 78)
    print("controls (synthetic fixture):")
    bad = self_test()
    print("controls (real table):")
    bad += real_controls(table)
    if bad:
        raise SystemExit("import_census: %d control rows failed — "
                         "the census does not run on a broken instrument" % bad)

    with open(opts.sweep, "r", encoding="utf-8") as f:
        sweep = json.load(f)
    refusing = [r for r in sweep["files"] if r.get("verdict") == "REFUSE"]
    on_import = [r for r in refusing if "import" in r.get("walls", [])]
    sole = [r for r in on_import if r["walls"] == ["import"]]
    plus = [r for r in on_import if len(r["walls"]) > 1]
    print("=" * 78)
    print("sweep: %d files, %d REFUSE; %d refuse with `import` in the wall "
          "set (%d sole-blocker, %d import+other)"
          % (len(sweep["files"]), len(refusing), len(on_import),
             len(sole), len(plus)))

    rows = []
    for r in on_import:
        path = r["file"]
        name = os.path.basename(path)[:-3]
        row = classify(table, os.path.abspath(path), name)
        row["walls"] = r["walls"]
        row["bucket"] = "import-only" if r["walls"] == ["import"] else "import+other"
        rows.append(row)

    print("=" * 78)
    for bucket in ("import-only", "import+other"):
        sub = [r for r in rows if r["bucket"] == bucket]
        counts = collections.Counter(r["verdict"] for r in sub)
        print("%-13s %3d files:  %s" % (bucket, len(sub),
              "  ".join("%s=%d" % (v, counts[v]) for v in
                        ("PURE", "PURE-ACCEL", "C-BLOCKED", "UNRESOLVED",
                         "NO-IMPORT") if counts.get(v))))
    counts = collections.Counter(r["verdict"] for r in rows)
    admissible = counts.get("PURE", 0) + counts.get("PURE-ACCEL", 0)
    print("CEILING: %d/%d refusing-on-import files could be admitted by a "
          "Python-only module system (%d PURE + %d PURE-ACCEL); %d are "
          "C-blocked, %d unresolved"
          % (admissible, len(rows), counts.get("PURE", 0),
             counts.get("PURE-ACCEL", 0), counts.get("C-BLOCKED", 0),
             counts.get("UNRESOLVED", 0)))

    winners = [r for r in rows if r["verdict"] in ("PURE", "PURE-ACCEL")]
    if winners:
        print("-" * 78)
        print("the admissible files, ranked by closure in-degree (how many "
              "other admissible files' closures contain them):")
        names = set(r["module"] for r in winners)
        indeg = {r["module"]:
                 sum(1 for t in winners if t is not r
                     and r["module"] in t["full"]["modules"])
                 for r in winners}
        for r in sorted(winners, key=lambda r: (-indeg[r["module"]],
                                                r["module"])):
            forms = import_forms(table, r)
            print("  %-24s %-10s unlocks %2d  closure %2d  forms %s"
                  % (r["module"], r["verdict"], indeg[r["module"]],
                     len(r["full"]["modules"]),
                     " ".join("%s=%d" % kv for kv in sorted(forms.items()))
                     or "-"))
            if r["optional_missing"]:
                print("      optional-missing (guarded, noted): %s"
                      % ", ".join(r["optional_missing"]))
        print("  pure NON-SEED modules most demanded across admissible "
              "closures:")
        demand = collections.Counter()
        for t in winners:
            for m in t["full"]["modules"]:
                if m != t["module"] and m not in names \
                        and table.resolve(m)[0] == "pure":
                    demand[m] += 1
        for m, n in demand.most_common(opts.top):
            print("    %3d  %s" % (n, m))

    unresolved = [r for r in rows if r["verdict"] == "UNRESOLVED"]
    if unresolved:
        print("-" * 78)
        print("UNRESOLVED — reported, never folded into pure:")
        for r in unresolved:
            for m in r["strict"]["missing"]:
                print("  %-24s %s" % (r["module"], chain(r["strict"], m)))

    dyn = sorted(set(m for r in rows for m in r["full"]["dynamic"]))
    print("-" * 78)
    print("%d closure modules contain a DYNAMIC import (`__import__`/"
          "`import_module`) the static walk cannot follow: %s"
          % (len(dyn), ", ".join(dyn[:14]) + (" ..." if len(dyn) > 14 else "")))

    if opts.json_out:
        slim = []
        for r in rows:
            slim.append({
                "module": r["module"], "file": r["file"],
                "bucket": r["bucket"], "walls": r["walls"],
                "verdict": r["verdict"],
                "closure": sorted(r["full"]["modules"]),
                "strict_c": r["strict"]["c"], "full_c": r["full"]["c"],
                "unresolved": r["strict"]["missing"],
                "optional_missing": r["optional_missing"],
                "dynamic": r["full"]["dynamic"],
                "forms": import_forms(table, r)
                if r["verdict"] in ("PURE", "PURE-ACCEL") else None})
        with open(opts.json_out, "w", encoding="utf-8") as f:
            json.dump({"cpython": table.version, "lib": table.lib,
                       "sweep": opts.sweep, "rows": slim}, f, indent=2)
            f.write("\n")
        print("wrote %s" % opts.json_out)
    return 0


if __name__ == "__main__":
    sys.exit(main())
