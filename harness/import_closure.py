#!/usr/bin/env python3
"""import_closure.py — the IMPORT CEILING, measured before it is committed to.

    python3 harness/import_closure.py [PATH_OR_GLOB ...] [--stdlib]
                                      [--cpython python3.9] [--json OUT]
                                      [--top N] [--list KIND] [--why MODULE]

THE QUESTION. `import` is leanpy's frontier: of the CPython 3.9 stdlib files
the completeness sweep refuses on, it is present in 155 and SOLE blocker in 7
(docs/backlog.md), and THE ONE PIPELINE made a Python-only module system
conceivable for the first time — importing a pure-Python module IS running its
top level in its own namespace, which is exactly what `runScript` does. But a
pure-Python module that imports a C one is still blocked, so the option is
worth only what its TRANSITIVE CLOSURE is worth. This measures that ceiling.

THE ANSWER IS A SPLIT, per seed file:

  NO-IMPORT    the file imports nothing — `import` is not its wall at all
  PURE         every module in the transitive closure is pure Python, so a
               Python-only module system could in principle run it
  C-REACHING   the closure contains a C builtin or an extension module; no
               Python-only module system can ever run it
  UNRESOLVED   the closure names a module this platform does not have
               (Windows-only branches) and no C module — reported apart,
               never folded into PURE

and, because a static closure can be drawn generously or meanly and the honest
number is the one that does not flatter, THREE are computed for every seed:

  IMPORT-TIME    the imports in the module BODY, including those under a
                 module-level `if`/`try`/`for`. THIS IS THE ONE WITH THE
                 SEMANTICS: an `import` executes when its statement runs, so
                 this is exactly the set a module system must satisfy to run
                 the file's top level.
  UNCONDITIONAL  only the imports that are direct children of the module body
                 — statically CERTAIN to execute, hence a LOWER bound that no
                 platform-branch or `except ImportError` fallback inflates.
  WHOLE-PROGRAM  every import anywhere, function bodies included — the UPPER
                 bound, what the file needs if every one of its functions is
                 eventually called.

A verdict that is C-REACHING even under UNCONDITIONAL is not an artifact of
static over-approximation: those imports run.

NOTHING IS IMPORTED. Every module is located on disk and parsed with `ast`;
resolving a name by importing it would run arbitrary stdlib top level, which is
exactly what the survey's safety list exists to avoid.

THE C CORE. When the answer is "C-reaching", the follow-up decision is how big
a native surface would have to be faked to change it. The report ends with THE
C SURFACE (how many distinct C modules, and how few any single seed needs) and
a GREEDY COVER: the C modules ranked by how many additional seeds each frees
once it and everything before it are native. A seed is freed only when EVERY C
module in its closure is provided, so this is a set cover and not a frequency
histogram — the module that tops the frequency list can free nobody. That
curve, not the pure/C split alone, is what prices a module system.

`--why MODULE` prints the import chain from a seed to each C module it reaches,
so every verdict this tool prints can be checked by hand against the source.

Python 3.9 compatible.
"""

import argparse
import ast
import collections
import glob
import json
import os
import subprocess
import sys

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# The stdlib sweep's SAFETY LIST, pinned here because it was previously an
# unrecorded `--exclude` regex: 167 = 174 top-level `.py` files minus these
# seven, whose top level (or `__main__` block, which leanpy DOES run since
# `__name__` is supplied) opens a browser, opens a window, or reaches the
# network.
SAFETY = ("antigravity", "webbrowser", "turtle",
          "nntplib", "smtpd", "telnetlib", "imaplib")

MAGIC = "*?["


# ---------------------------------------------------------------------------
# the module table — built by LOOKING, never by importing
# ---------------------------------------------------------------------------

class ModuleTable(object):
    """Resolves a dotted module name against one CPython installation."""

    def __init__(self, lib, builtins, dynload, version):
        self.lib = lib
        self.builtins = frozenset(builtins)
        self.dynload = set(dynload)
        self.version = version
        self._memo = {}

    @classmethod
    def of(cls, cpython):
        """The table of one installed interpreter — asked, never imported."""
        out = subprocess.run(
            [cpython, "-c", "import sys, sysconfig;"
             "print(sysconfig.get_paths()['stdlib']);"
             "print(' '.join(sys.builtin_module_names));"
             "print(sys.version.split()[0])"],
            capture_output=True, text=True)
        if out.returncode != 0:
            raise SystemExit("import_closure: %s is not runnable: %s"
                             % (cpython, out.stderr.strip()))
        lib, builtins, version = out.stdout.splitlines()[:3]
        dynload = set()
        d = os.path.join(lib, "lib-dynload")
        if os.path.isdir(d):
            for f in os.listdir(d):
                if f.endswith((".so", ".pyd", ".dylib")):
                    dynload.add(f.split(".")[0])
        return cls(lib, builtins.split(), dynload, version)

    def resolve(self, name):
        """(kind, path) with kind in pure / c-builtin / c-ext / missing."""
        if name in self._memo:
            return self._memo[name]
        parts = name.split(".")
        r = None
        p = os.path.join(self.lib, *parts) + ".py"
        if os.path.isfile(p):
            r = ("pure", p)
        if r is None:
            p = os.path.join(self.lib, *(parts + ["__init__.py"]))
            if os.path.isfile(p):
                r = ("pure", p)
        if r is None and name in self.builtins:
            r = ("c-builtin", None)
        if r is None and parts[-1] in self.dynload and len(parts) == 1:
            r = ("c-ext", None)
        if r is None:
            # a submodule of a package that resolves to an extension, or a
            # name this platform does not ship at all
            r = ("missing", None)
        self._memo[name] = r
        return r


# ---------------------------------------------------------------------------
# static imports
# ---------------------------------------------------------------------------

def _prefixes(dotted):
    """`a.b.c` -> a, a.b, a.b.c — CPython imports every parent package."""
    parts = dotted.split(".")
    return [".".join(parts[:i]) for i in range(1, len(parts) + 1)]


def _from_targets(node, base):
    """(certain, maybe) module names one `ImportFrom` demands.

    `from p import x` binds either p's submodule `p.x` or p's attribute `x`,
    and only the module table can tell which — so `p.x` is MAYBE: followed
    when it resolves, silently dropped when it does not. Counting it as a
    missing module is how `from os import getcwd` would fake a hole.
    """
    if node.level:
        anc = base.split(".")
        drop = node.level - 1
        anc = anc[:len(anc) - drop] if drop else anc
        root = ".".join(anc)
        mod = root + ("." + node.module if node.module else "")
    else:
        mod = node.module or ""
    if not mod:
        return [], []
    maybe = [mod + "." + a.name for a in node.names if a.name != "*"]
    return _prefixes(mod), maybe


class FileImports(object):
    """The import names of one source file, at three scopes.

    `top` is the one with the semantics: an `import` executes when the
    statement containing it runs, so the IMPORT-TIME closure is the imports in
    the module BODY — including those under a module-level `if`/`try`/`for` —
    and NOT the ones inside a `def` or `class` body, which run only if that
    function is called.

    Each scope maps a module name to two flags:
      main   the import sits under `if __name__ == "__main__":`, so it runs
             when the file is a PROGRAM and never when it is IMPORTED;
      maybe  it came from `from p import x`, so it is a module only if it
             resolves to one (otherwise x is an attribute of p).
    """

    def __init__(self, scopes, dynamic, broken=False):
        self.scopes = scopes        # {scope: {name: (main, maybe)}}
        self.dynamic = dynamic
        self.broken = broken

    def demands(self, scope, as_program):
        """[(name, maybe)] this file needs in that scope, run that way."""
        return [(n, mb) for n, (mn, mb) in self.scopes[scope].items()
                if as_program or not mn]


def _is_main_guard(node):
    """`if __name__ == "__main__":` — the block CPython skips on import.

    Counting it as an import-time dependency is how `heapq` acquires `doctest`
    (and through it `pdb`, `unittest`, `signal`, `time`) in a closure it never
    actually pulls: heapq's guard is dead the moment heapq is imported. The
    seed file is the one exception — leanpy supplies `__name__ = "__main__"`,
    so a file run as a PROGRAM does execute its guard.
    """
    if not isinstance(node, ast.If):
        return False
    t = node.test
    if not isinstance(t, ast.Compare) or len(t.ops) != 1:
        return False
    if not isinstance(t.ops[0], (ast.Eq, ast.In)):
        return False
    sides = [t.left] + list(t.comparators)
    names = [s.id for s in sides if isinstance(s, ast.Name)]
    consts = []
    for s in sides:
        if isinstance(s, ast.Constant):
            consts.append(s.value)
        elif isinstance(s, (ast.Tuple, ast.List)):
            consts.extend(e.value for e in s.elts if isinstance(e, ast.Constant))
    return "__name__" in names and "__main__" in consts


_PARSE_MEMO = {}


def imports_of(path, modname):
    key = (path, modname)
    if key not in _PARSE_MEMO:
        _PARSE_MEMO[key] = _imports_of(path, modname)
    return _PARSE_MEMO[key]


_SCOPED = (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef, ast.Lambda)


SCOPES = ("top", "uncond", "all")


def _imports_of(path, modname):
    empty = dict((s, {}) for s in SCOPES)
    try:
        with open(path, "rb") as f:
            tree = ast.parse(f.read())
    except (SyntaxError, ValueError, OSError, UnicodeDecodeError):
        return FileImports(empty, False, broken=True)
    # relative imports resolve against the PACKAGE: a package's own name, a
    # plain module's parent.
    ispkg = os.path.basename(path) == "__init__.py"
    base = modname if ispkg else (modname.rsplit(".", 1)[0] if "." in modname
                                  else modname)
    scopes = dict((s, {}) for s in SCOPES)
    dynamic = False
    direct = set(id(s) for s in tree.body)

    def record(scope, name, main, maybe):
        prev = scopes[scope].get(name)
        # a name imported both ways is unguarded and certain: take the weaker
        # flags, never the stronger — an OR here would invent a dependency.
        scopes[scope][name] = ((main and prev[0], maybe and prev[1])
                               if prev else (main, maybe))

    def walk(node, in_body, main):
        """`in_body`: no def/class/lambda crossed. `main`: under a guard."""
        nonlocal dynamic
        certain, mods = None, []
        if isinstance(node, ast.Import):
            certain = [m for a in node.names for m in _prefixes(a.name)]
        elif isinstance(node, ast.ImportFrom):
            certain, mods = _from_targets(node, base)
        elif isinstance(node, ast.Call):
            fn = node.func
            nm = getattr(fn, "id", None) or getattr(fn, "attr", None)
            if nm in ("__import__", "import_module"):
                dynamic = True
        if certain is not None:
            for m in certain:
                record("all", m, main, False)
            for m in mods:
                record("all", m, main, True)
            if in_body:
                for m in certain:
                    record("top", m, main, False)
                for m in mods:
                    record("top", m, main, True)
                if id(node) in direct:
                    for m in certain:
                        record("uncond", m, main, False)
                    for m in mods:
                        record("uncond", m, main, True)
        inner = in_body and not isinstance(node, _SCOPED)
        if not main and _is_main_guard(node):
            # only the GUARDED branch is program-only; the `else:` of a
            # `__main__` guard is what runs on import.
            for child in node.body:
                walk(child, inner, True)
            for child in node.orelse:
                walk(child, inner, False)
            return
        for child in ast.iter_child_nodes(node):
            walk(child, inner, main)

    for stmt in tree.body:
        walk(stmt, True, False)
    return FileImports(scopes, dynamic)


# ---------------------------------------------------------------------------
# the closure
# ---------------------------------------------------------------------------

def closure(table, seed_path, seed_name, field):
    """BREADTH-first from one seed. Returns a dict of the walked facts.

    Breadth-first is not a taste: the reported distance from a seed to its
    nearest C module is only the true distance if the frontier is a QUEUE. A
    depth-first walk with a `seen` set records whatever depth it happened to
    reach a module by first, which is an instrument that lies.
    """
    seen = {seed_name: 0}
    via = {}                     # module -> the module that imported it
    kinds = {}
    dyn = set()
    broken = set()
    frontier = collections.deque([(seed_name, seed_path, 0)])
    while frontier:
        name, path, depth = frontier.popleft()
        fi = imports_of(path, name)
        if fi.broken:
            broken.add(name)
            continue
        if fi.dynamic:
            dyn.add(name)
        # The SEED runs as a program (leanpy supplies `__name__ == "__main__"`);
        # everything below it is being imported, so its `__main__` guard is
        # dead. `from p import x`: a name that resolves IS a submodule; one
        # that does not is an attribute of p, not a hole in the platform.
        for m, drop_missing in sorted(fi.demands(field, depth == 0)):
            if m in seen:
                continue
            kind, p = table.resolve(m)
            if drop_missing and kind == "missing":
                continue
            seen[m] = depth + 1
            via[m] = name
            kinds[m] = kind
            if kind == "pure":
                frontier.append((m, p, depth + 1))
    cmods = sorted(m for m, k in kinds.items() if k in ("c-builtin", "c-ext"))
    missing = sorted(m for m, k in kinds.items() if k == "missing")
    if len(seen) == 1:
        verdict = "NO-IMPORT"
    elif cmods:
        verdict = "C-REACHING"
    elif missing:
        verdict = "UNRESOLVED"
    else:
        verdict = "PURE"
    return {"verdict": verdict, "size": len(seen), "c": cmods,
            "missing": missing, "dynamic": sorted(dyn), "broken": sorted(broken),
            "c_depth": min([seen[m] for m in cmods], default=None),
            "via": via, "modules": sorted(seen)}


def path_to(rec, target):
    """The import chain seed -> … -> target, read off the BFS parents."""
    via = rec["via"]
    chain = [target]
    while chain[-1] in via:
        chain.append(via[chain[-1]])
    return " -> ".join(reversed(chain))


# ---------------------------------------------------------------------------

# ---------------------------------------------------------------------------
# is "reaches C" fatal?  Not uniformly — and the split is a JUDGMENT
# ---------------------------------------------------------------------------
# `itertools` is a C module and leanpy already models `itertools.count`; so
# "C-reaching" on its own would be a scary word for a solvable problem, and a
# report that stopped there would be as mis-ranked as the class tier was. The
# distinction that decides the question is not implementation language, it is
# KIND: a C module that is pure computation is a Lean definition someone can
# write, while a C module that IS the operating system, the IO layer, the
# thread scheduler, or the interpreter's reflection of itself cannot be
# modelled without inventing the thing it reflects — the pass-8 UCI verdict,
# "out of scope BY KIND, not by distance".
#
# The membership below is an argued call, not a measurement. It is written out
# so it can be disagreed with line by line, and the report prints both numbers
# either way.

BY_KIND = frozenset((
    # operating system, process, filesystem, terminal
    "posix", "nt", "fcntl", "grp", "pwd", "_posixsubprocess", "select",
    "termios", "readline", "_crypt", "_curses", "syslog", "resource",
    # the IO layer, the network
    "_io", "_socket", "_ssl", "_asyncio",
    # concurrency
    "_thread", "_queue", "_contextvars", "_signal", "_multiprocessing",
    # the interpreter reflecting on itself: frames, modules, bytecode, GC
    "sys", "builtins", "_imp", "marshal", "_ast", "_symtable", "_opcode",
    "_warnings", "_weakref", "gc", "_tracemalloc", "_lsprof", "atexit",
    "faulthandler", "_frozen_importlib", "_frozen_importlib_external",
    # nondeterminism and environment
    "_random", "_uuid", "time", "_locale", "_datetime",
))


def kind_split(cmods):
    """(modellable, by-kind) — which half of the C set is the real wall."""
    return ([m for m in cmods if m not in BY_KIND],
            [m for m in cmods if m in BY_KIND])


# ---------------------------------------------------------------------------
# THE SELF-TEST
# ---------------------------------------------------------------------------
# A tool that answers "C-REACHING" for every input would print exactly the
# headline this one prints — 0 pure closures — and would be worth nothing.
# So the fixture below is built to make it say PURE, and to make each of the
# four judgment calls in the walk visible as its own falsifiable row. If
# `--self-test` cannot get a PURE verdict out of a closure that is pure, the
# 0/155 is a bug report about this file and not a fact about CPython.

FIXTURE = {
    # a pure chain, two hops: the case the stdlib has none of
    "purely.py":        "import midway\n",
    "midway.py":        "import leaf\n",
    "leaf.py":          "X = 1\n",
    # C at one hop, C at two hops
    "direct_c.py":      "import _speedups\n",
    "deep_c.py":        "import viac\n",
    "viac.py":          "import _speedups\n",
    # the `__main__` guard: live for the seed, dead for anything importing it
    "guarded.py":       "import leaf\nif __name__ == '__main__':\n    import _speedups\n",
    "imports_guarded.py": "import guarded\n",
    # `from p import x` where x is an ATTRIBUTE, not a submodule
    "attr_only.py":     "from leaf import X\n",
    # ... and where it IS a submodule, reached only through the maybe pass
    "pkg/__init__.py":  "PKG = 1\n",
    "pkg/sub.py":       "import _speedups\n",
    "subimport.py":     "from pkg import sub\n",
    # a function-body import: whole-program only, never import-time
    "lazy.py":          "def go():\n    import _speedups\n    return _speedups\n",
    # a module-level `try:` — import-time, but not UNCONDITIONAL
    "tried.py":         "try:\n    import _speedups\nexcept ImportError:\n    pass\n",
}

# (seed, scope, expected verdict, expected C modules) — each row is a claim
# that would break if one of the four judgment calls were wrong.
SELF_TEST = [
    ("purely",          "top", "PURE",       []),
    ("leaf",            "top", "NO-IMPORT",  []),
    ("direct_c",        "top", "C-REACHING", ["_speedups"]),
    ("deep_c",          "top", "C-REACHING", ["_speedups"]),
    ("guarded",         "top", "C-REACHING", ["_speedups"]),
    ("imports_guarded", "top", "PURE",       []),
    ("attr_only",       "top", "PURE",       []),
    ("subimport",       "top", "C-REACHING", ["_speedups"]),
    ("lazy",            "top", "NO-IMPORT",  []),
    ("lazy",            "all", "C-REACHING", ["_speedups"]),
    ("tried",           "top", "C-REACHING", ["_speedups"]),
    ("tried",        "uncond", "NO-IMPORT",  []),
]


def self_test():
    """Build the fixture, walk it, and check every row. Returns an exit code."""
    import shutil
    import tempfile
    root = tempfile.mkdtemp(prefix="import-closure-selftest-")
    try:
        for rel, src in FIXTURE.items():
            path = os.path.join(root, rel)
            os.makedirs(os.path.dirname(path), exist_ok=True)
            with open(path, "w", encoding="utf-8") as f:
                f.write(src)
        table = ModuleTable(root, ["_speedups"], [], "fixture")
        bad = 0
        for seed, scope, want_v, want_c in SELF_TEST:
            rec = closure(table, os.path.join(root, seed + ".py"), seed, scope)
            got_v, got_c = rec["verdict"], rec["c"]
            ok = got_v == want_v and got_c == want_c
            bad += 0 if ok else 1
            print("  %-4s %-16s %-7s want %-11s %-14s got %-11s %s"
                  % ("ok" if ok else "FAIL", seed, scope, want_v,
                     ",".join(want_c) or "-", got_v, ",".join(got_c) or "-"))
        # depth is a claim too, and a depth-first walk would get it wrong
        rec = closure(table, os.path.join(root, "deep_c.py"), "deep_c", "top")
        ok = rec["c_depth"] == 2
        bad += 0 if ok else 1
        print("  %-4s deep_c           top     want c_depth 2                got "
              "c_depth %s" % ("ok" if ok else "FAIL", rec["c_depth"]))
        print("SELF-TEST: %d of %d rows failed" % (bad, len(SELF_TEST) + 1))
        return 1 if bad else 0
    finally:
        shutil.rmtree(root, ignore_errors=True)


def tier_census(table, modules, cache):
    """{module: [wall ...]} — the SECOND ceiling.

    "Pure Python" is not the same as "leanpy can run it". A module system that
    imports a pure-Python module still has to EXECUTE its top level, so the
    modules in the closures are themselves subject to the tier. This extracts
    each one and reuses the survey's static wall census; a module whose only
    wall is `import` is one the module system itself would resolve, so that
    wall is discounted and everything else is a real second-layer blocker.
    """
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import leanpy_survey
    os.makedirs(cache, exist_ok=True)
    extract = os.path.join(REPO_ROOT, "extractors", "python", "extract.py")
    out = {}
    for i, (name, path) in enumerate(sorted(modules.items())):
        env = os.path.join(cache, "closure-%04d.json" % i)
        proc = subprocess.run([sys.executable, extract, path, "--out", env],
                              capture_output=True, text=True, cwd=REPO_ROOT)
        if proc.returncode != 0 or not os.path.isfile(env):
            out[name] = ["extract-failed"]
            continue
        _, _, walls = leanpy_survey.census(env)
        out[name] = [w for w in walls if w != "import"]
    return out


def expand(patterns):
    out = []
    for pat in patterns:
        if os.path.isdir(pat):
            pat = os.path.join(pat, "*.py")
        hits = sorted(glob.glob(pat)) if any(c in pat for c in MAGIC) else [pat]
        for h in hits:
            if h.endswith(".py") and os.path.isfile(h) and h not in out:
                out.append(h)
    return out


def stdlib_seeds(table):
    names = sorted(f[:-3] for f in os.listdir(table.lib) if f.endswith(".py"))
    return [os.path.join(table.lib, n + ".py")
            for n in names if n not in SAFETY]


def greedy_cover(rows, limit):
    """[(module, seeds newly freed, seeds freed so far)] — the price list.

    A seed becomes runnable under a Python-only module system exactly when
    EVERY C module in its closure is provided natively, so the useful ranking
    is a set cover, not a frequency histogram: the module that tops the
    frequency list may free nobody at all.
    """
    remaining = [set(r["c"]) for r in rows if r["c"]]
    provided = set()
    out = []
    freed = 0
    for _ in range(limit):
        need = {}
        for cs in remaining:
            for m in cs - provided:
                need[m] = need.get(m, 0) + 1
        if not need:
            break
        # pick the module that appears in the most still-blocked closures
        pick = max(sorted(need), key=lambda m: need[m])
        provided.add(pick)
        now = [cs for cs in remaining if cs - provided]
        gained = len(remaining) - len(now)
        remaining = now
        freed += gained
        out.append((pick, gained, freed))
    return out


def main(argv=None):
    p = argparse.ArgumentParser(prog="import_closure.py")
    p.add_argument("paths", nargs="*", metavar="PATH_OR_GLOB")
    p.add_argument("--stdlib", action="store_true",
                   help="seed with the stdlib sweep's 167 top-level modules")
    p.add_argument("--cpython", default=os.environ.get("LEANPY_CPYTHON")
                   or "python3.9")
    p.add_argument("--top", type=int, default=15)
    p.add_argument("--list", default=None, metavar="VERDICT",
                   help="print every seed with this verdict")
    p.add_argument("--self-test", dest="self_test", action="store_true",
                   help="walk a synthetic fixture built to make this tool say "
                   "PURE, and check every judgment call in the walk")
    p.add_argument("--tier", action="store_true",
                   help="also census every pure-Python module in the closures "
                   "against the leanpy tier (the SECOND ceiling); extracts one "
                   "envelope per module, so it costs a minute")
    p.add_argument("--cache", default=os.path.join(
        os.environ.get("TMPDIR", "/tmp"), "leanpy-closure-cache"))
    p.add_argument("--why", default=None, metavar="MODULE",
                   help="print the import chain from that seed to every C "
                   "module it reaches (the instrument's own audit trail)")
    p.add_argument("--json", dest="json_out", default=None)
    opts = p.parse_args(argv)

    if opts.self_test:
        return self_test()
    table = ModuleTable.of(opts.cpython)
    seeds = expand(opts.paths)
    if opts.stdlib or not seeds:
        seeds = stdlib_seeds(table) + seeds
    if not seeds:
        raise SystemExit("import_closure: no seed files")

    print("reference: CPython %s at %s" % (table.version, table.lib))
    print("%d builtin modules, %d extension modules in lib-dynload"
          % (len(table.builtins), len(table.dynload)))
    print("%d seed files" % len(seeds))

    rows = []
    for path in seeds:
        name = os.path.basename(path)[:-3]
        rec = {"file": path, "module": name}
        for tag in ("top", "uncond", "all"):
            rec[tag] = closure(table, path, name, tag)
        rows.append(rec)

    for tag, label in (
            ("top", "IMPORT-TIME closure — imports in the module BODY (the one "
                    "with the semantics)"),
            ("uncond", "UNCONDITIONAL only — direct children of the module body "
                       "(lower bound)"),
            ("all", "WHOLE-PROGRAM — every import, function bodies included "
                    "(upper bound)")):
        counts = {}
        for r in rows:
            v = r[tag]["verdict"]
            counts[v] = counts.get(v, 0) + 1
        print("=" * 78)
        print(label)
        for v in ("NO-IMPORT", "PURE", "UNRESOLVED", "C-REACHING"):
            print("  %-12s %4d" % (v, counts.get(v, 0)))
        importing = len(rows) - counts.get("NO-IMPORT", 0)
        if importing:
            pure = counts.get("PURE", 0)
            print("  CEILING: %d/%d = %.1f%% of the files that import at all "
                  "could be reached by a PYTHON-ONLY module system"
                  % (pure, importing, 100.0 * pure / importing))
        depths = [r[tag]["c_depth"] for r in rows if r[tag]["c_depth"]]
        if depths:
            hist = {}
            for d in depths:
                hist[d] = hist.get(d, 0) + 1
            print("  distance from the seed to the nearest C module: "
                  + ", ".join("%d hop%s=%d" % (d, "" if d == 1 else "s", hist[d])
                              for d in sorted(hist)))
        if opts.list == tag or opts.list in ("PURE", "UNRESOLVED", "NO-IMPORT"):
            want = opts.list if opts.list in ("PURE", "UNRESOLVED",
                                              "NO-IMPORT") else None
            for r in rows:
                if want is None or r[tag]["verdict"] == want:
                    print("    %-12s %-32s closure %d, %d C"
                          % (r[tag]["verdict"], r["module"], r[tag]["size"],
                             len(r[tag]["c"])))

    print("=" * 78)
    creach = [r for r in rows if r["top"]["verdict"] == "C-REACHING"]
    union = set()
    for r in creach:
        union.update(r["top"]["c"])
    print("THE C SURFACE: %d distinct C modules across %d import-time closures"
          % (len(union), len(creach)))
    if creach:
        hist = {}
        for r in creach:
            n = len(r["top"]["c"])
            hist[n] = hist.get(n, 0) + 1
        cheapest = sorted(creach, key=lambda r: (len(r["top"]["c"]), r["module"]))
        print("  C modules a single seed needs: min %d, median %d, max %d"
              % (len(cheapest[0]["top"]["c"]),
                 len(cheapest[len(cheapest) // 2]["top"]["c"]),
                 len(cheapest[-1]["top"]["c"])))
        print("  the CHEAPEST seeds — the ones a small native core would reach "
              "first:")
        for r in cheapest[:8]:
            print("    %-22s %d C: %s" % (r["module"], len(r["top"]["c"]),
                                          ", ".join(r["top"]["c"])))
    print("-" * 78)
    print("IS \"reaches C\" FATAL? — the C set split by KIND (an argued call, "
          "BY_KIND in the source):")
    only_model, has_kind, kindfreq = 0, 0, {}
    for r in creach:
        model, kind = kind_split(r["top"]["c"])
        if kind:
            has_kind += 1
            for m in kind:
                kindfreq[m] = kindfreq.get(m, 0) + 1
        else:
            only_model += 1
    print("  %d seeds reach ONLY computational C modules (itertools, _sre, "
          "math, _struct …) — Lean definitions someone could write" % only_model)
    print("  %d seeds reach at least one BY-KIND module — the OS, the IO "
          "layer, threads, or the interpreter's reflection of itself"
          % has_kind)
    for m, n in sorted(kindfreq.items(), key=lambda kv: (-kv[1], kv[0]))[:6]:
        print("      %4d seeds blocked by %s" % (n, m))
    freq = {}
    for r in rows:
        for m in r["top"]["c"]:
            freq[m] = freq.get(m, 0) + 1
    print("-" * 78)
    print("C modules by how many seed closures contain them:")
    for m, n in sorted(freq.items(), key=lambda kv: (-kv[1], kv[0]))[:opts.top]:
        print("  %4d  %s" % (n, m))

    print("-" * 78)
    print("GREEDY COVER — a seed is freed only when EVERY C module in its "
          "closure is native:")
    cover = greedy_cover([r["top"] for r in rows], opts.top)
    blocked = sum(1 for r in rows if r["top"]["c"])
    for m, gained, freed in cover:
        print("  + %-24s frees %3d more   (%d/%d C-reaching seeds)"
              % (m, gained, freed, blocked))
    if cover and cover[-1][2] == 0:
        print("  ...the first %d native C modules free NOTHING: no seed's "
              "closure is a subset of them." % len(cover))

    if opts.tier:
        pure = {}
        for r in rows:
            for m in r["top"]["modules"]:
                kind, p = table.resolve(m)
                if kind == "pure" and m not in pure:
                    pure[m] = p
        walls = tier_census(table, pure, opts.cache)
        clean = [m for m, w in walls.items() if not w]
        print("-" * 78)
        print("THE SECOND CEILING — pure-Python is not the same as in-tier:")
        print("  %d distinct pure-Python modules appear in the import-time "
              "closures" % len(pure))
        print("  %d of them (%.1f%%) have NO static wall besides `import`, so "
              "a module system could run their top level as it stands"
              % (len(clean), 100.0 * len(clean) / max(len(pure), 1)))
        # RANK THE LIBRARY TAIL THE SAME WAY THE SEED TIER IS RANKED. The
        # lesson of the last two milestones is that a `present` count can hide
        # behind another wall, so the tail gets `sole` beside it — and, because
        # these walls co-occur heavily where `import` did not, a BATCH curve
        # too: what N constructs closed TOGETHER would buy, which is the unit
        # of work the co-occurrence makes real.
        blocked_mods = {m: w for m, w in walls.items() if w}
        wf, sole = {}, {}
        for m, w in blocked_mods.items():
            for x in w:
                wf[x] = wf.get(x, 0) + 1
            if len(w) == 1:
                sole[w[0]] = sole.get(w[0], 0) + 1
        print("  %d of the %d are blocked by something; ranked `sole` beside "
              "`present`, as the seed tiers are:"
              % (len(blocked_mods), len(pure)))
        for x in sorted(wf, key=lambda x: (-sole.get(x, 0), -wf[x]))[:opts.top]:
            print("    sole %4d   present %4d   %s" % (sole.get(x, 0), wf[x], x))
        print("  BATCH CURVE — modules freed when these walls fall TOGETHER "
              "(a module needs ALL of its walls gone):")
        batch = greedy_cover([{"c": w} for w in blocked_mods.values()], opts.top)
        for x, gained, freed in batch:
            print("    + %-22s frees %3d more   (%d/%d blocked modules)"
                  % (x, gained, freed, len(blocked_mods)))
        # The compound ceiling: BOTH gates open. Counted with the C gate
        # assumed away entirely — a strictly generous hypothesis, so the
        # number below is an upper bound on what any module system can reach.
        ok = []
        for r in rows:
            if r["top"]["verdict"] == "NO-IMPORT":
                continue
            pures = [m for m in r["top"]["modules"]
                     if table.resolve(m)[0] == "pure" and m != r["module"]]
            if all(not walls.get(m, ["?"]) for m in pures):
                ok.append(r["module"])
        importing = sum(1 for r in rows if r["top"]["verdict"] != "NO-IMPORT")
        print("  COMPOUND: even GRANTING every C module natively, only %d/%d "
              "importing seeds have every pure-Python module in their closure "
              "in tier (the seed's OWN other walls are not counted here — the "
              "survey's `sole` telemetry is where those live):"
              % (len(ok), importing))
        print("    " + ", ".join(ok))

    if opts.why:
        print("-" * 78)
        hits = [r for r in rows if r["module"] == opts.why]
        if not hits:
            raise SystemExit("import_closure: %s is not a seed" % opts.why)
        rec = hits[0]["top"]
        print("WHY %s is %s — the import-time chain to every C module it "
              "reaches:" % (opts.why, rec["verdict"]))
        for m in rec["c"]:
            print("    %s" % path_to(rec, m))

    dyn = [r["module"] for r in rows if r["top"]["dynamic"]]
    print("-" * 78)
    print("%d seeds reach a DYNAMIC import (`__import__`/`import_module`), "
          "which no static closure can follow: %s"
          % (len(dyn), ", ".join(dyn[:12]) + (" ..." if len(dyn) > 12 else "")))

    if opts.json_out:
        with open(opts.json_out, "w", encoding="utf-8") as f:
            json.dump({"cpython": table.version, "lib": table.lib,
                       "seeds": len(seeds), "rows": rows}, f, indent=2)
            f.write("\n")
        print("wrote %s" % opts.json_out)
    return 0


if __name__ == "__main__":
    sys.exit(main())
