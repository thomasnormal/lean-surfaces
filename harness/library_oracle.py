#!/usr/bin/env python3
"""library_oracle.py — the CPython half of LIBRARY MODE, in one subprocess.

    python3.9 harness/library_oracle.py --module NAME --file PATH --out OUT.json
                                        [--calls] [--max-calls N] [--call-timeout S]

LIBRARY MODE is the metric the owner named on 2026-08-15: "import this
module, then verify its public functions behave identically to CPython's
— we should be able to verify modules that we just import, but don't have
a way to run." Program mode (`harness/leanpy_survey.py`) runs a FILE and
compares stdout; a library has no stdout to compare, so its meaning lives
in what its functions RETURN.

This process is the reference half. It does four things and nothing else:

  1. EXECUTES THE MODULE BODY under IMPORT semantics — a fresh module
     object whose ``__name__`` is the module's import name, not
     ``"__main__"``. That distinction is the whole point of library mode
     and it is where the model has no counterpart yet (Script.lean's
     `scriptNameBinding` binds ``"__main__"``), so the driver gates on it.
  2. ENUMERATES the public functions: no leading underscore, a plain
     Python function, and DEFINED IN THIS FILE (`__code__.co_filename`) —
     a name re-exported from elsewhere is that module's obligation.
  3. BUILDS A DETERMINISTIC BATTERY per function: the function's own
     doctests first (they are the module author's own claims), then
     type-driven generated inputs from a fixed pool, sampled with a seed
     derived from ``crc32(module.function)``. No wall clock, no
     ``hash()`` (randomized per process), no ``set`` iteration in any
     ordering decision — the same bytes every run, on any box.
  4. RUNS each call and canonicalizes the outcome in the runner's own JSON
     form (harness/diff_test.py `to_canonical_value` — ints/bools/str/
     None/list/tuple), plus the two things the typed-call protocol cannot
     carry: the call's STDOUT, and whether it MUTATED its arguments.

It never decides a verdict. Comparison lives in the driver, which pairs
this file's rows against the model's.

SAFETY. This process imports and CALLS real stdlib code, so it is
isolated by construction: the driver hands it a scratch cwd, calls are
made with stdout captured, a per-call SIGALRM bounds a runaway loop, and
`UNSAFE_CALL` names the verbs that are never driven at all (a skipped
function is reported as data — it is a hole in the battery, and a hole
that is counted is not a hole that is hidden).

Python 3.9 compatible; run it UNDER 3.9 (the driver re-execs into the pin).
"""

import argparse
import ast
import copy
import doctest
import inspect
import io
import json
import os
import random
import re
import signal
import sys
import zlib

# ---------------------------------------------------------------------------
# the canonical value form — the runner's own encoding (DESIGN.md)
# ---------------------------------------------------------------------------

MAX_VALUE_NODES = 4096


class Unmappable(Exception):
    """A CPython value outside the canonical set (float, dict, object, …).

    NOT an error: the model's public value set is exactly this set, so a
    function returning anything else is a call the two sides cannot be
    compared on. It is reported and excluded, never guessed at."""


def to_canonical_value(v, budget=None):
    """Python value -> canonical V form. bool before int: bool is an int
    subtype. `budget` caps the node count so a function returning a
    million-element list cannot turn the manifest into a data dump."""
    if budget is None:
        budget = [MAX_VALUE_NODES]
    budget[0] -= 1
    if budget[0] < 0:
        raise Unmappable("value larger than %d nodes" % MAX_VALUE_NODES)
    if isinstance(v, bool):
        return {"t": "bool", "v": v}
    if isinstance(v, int):
        return {"t": "int", "v": str(v)}
    if isinstance(v, str):
        return {"t": "str", "v": v}
    if v is None:
        return {"t": "none"}
    if isinstance(v, list):
        return {"t": "list", "v": [to_canonical_value(x, budget) for x in v]}
    if isinstance(v, tuple):
        return {"t": "tuple", "v": [to_canonical_value(x, budget) for x in v]}
    raise Unmappable(type(v).__name__)


def from_canonical_value(a):
    """Canonical V form (or a plain int) -> the Python value."""
    if not isinstance(a, dict):
        return a
    t = a.get("t")
    if t == "none":
        return None
    if t == "bool":
        return bool(a["v"])
    if t == "int":
        return int(a["v"])
    if t == "str":
        return a["v"]
    if t == "list":
        return [from_canonical_value(x) for x in a["v"]]
    if t == "tuple":
        return tuple(from_canonical_value(x) for x in a["v"])
    raise ValueError("bad canonical value: %r" % (a,))


def exception_name(e):
    """The class name the model reports. `UnboundLocalError` is a NameError
    subclass and the interpreter reports the parent (DESIGN.md
    name-resolution row) — the one alias diff_test.py also applies."""
    name = type(e).__name__
    return "NameError" if name == "UnboundLocalError" else name


# ---------------------------------------------------------------------------
# the battery: doctests, then type-driven generation
# ---------------------------------------------------------------------------

# Verbs that reach outside the process. A public function whose name starts
# with one of these is NEVER driven — reported as `skipped: unsafe` so the
# module can never be called VERIFIED on a battery that quietly omitted it.
# Deliberately a NAME rule and not a cleverness: it can be read, argued
# with, and extended line by line.
UNSAFE_CALL = re.compile(
    r"^(open|remove|unlink|rmtree|rmdir|mkdir|makedirs|move|copy|chmod|chown|link|symlink|rename"
    r"|truncate|write|save|dump|load|system|popen|spawn|fork|exec|kill|abort|exit|quit|call|run"
    r"|check_|start|serve|listen|connect|bind|accept|send|recv|request|urlopen|retrieve|install"
    r"|register|unregister|main|interact|set_|reset|enable|disable|shutdown|close|flush|input"
    r"|compile_dir|compile_file|pdb|post_mortem|breakpoint|trace|profile|monitor|sleep)")

# The type-driven pools. Small, boring and FIXED: the battery's job is to
# be reproducible and to hit the boundaries the tier argues about (empty,
# singleton, negative, unicode), not to be a fuzzer.
POOLS = {
    "int": [0, 1, 2, -1, 7, 100],
    "str": ["", "a", "abc", "Hello, World", "  x  "],
    "bool": [True, False],
    "list": [[], [1], [1, 3, 5], [3, 1, 2], ["a", "b"]],
    "tuple": [(), (1,), (1, 2, 3)],
    "none": [None],
}

# What an annotation says, when it says anything this harness understands.
ANNOTATION_POOL = {
    "int": "int", "str": "str", "bool": "bool", "list": "list", "tuple": "tuple",
    "float": None, "bytes": None, "dict": None, "set": None, "object": None,
}

# The generic pool for an unannotated parameter — one value of each shape,
# in a fixed order, so an unannotated function is still driven across the
# type boundary (where the TypeErrors live, which is where a silent
# divergence would hide).
GENERIC = ["int", "str", "list"]


def _seed_for(module, func):
    """A stable per-function seed. `crc32`, not `hash()`: `hash()` of a str
    is salted per process (PYTHONHASHSEED), which would make the battery a
    different battery on every run — the one thing it must never be."""
    return zlib.crc32(("%s.%s" % (module, func)).encode("utf-8"))


class _Param(object):
    """One parameter of a file-defined function: name, annotation SOURCE
    TEXT (never an evaluated object — evaluating an annotation runs code),
    whether it has a default, and the default's literal value when the
    default is a literal."""

    def __init__(self, d):
        self.name = d["name"]
        self.annotation = d.get("annotation")
        self.has_default = d.get("has_default", False)
        self.default = d.get("default")


def _pool_for(param):
    """The candidate values for one parameter, as a list of Python values."""
    kinds = None
    if param.annotation:
        base = param.annotation.split("[")[0].strip("'\" ")
        if base in ANNOTATION_POOL:
            mapped = ANNOTATION_POOL[base]
            kinds = [mapped] if mapped else []   # a known-unmappable annotation: drive nothing
    if kinds is None and param.has_default and param.default is not None:
        for kind, pool in POOLS.items():
            if kind != "none" and type(param.default) is type(pool[0]):
                kinds = [kind]
                break
    if kinds is None:
        kinds = list(GENERIC)
    out = []
    for kind in kinds:
        out.extend(POOLS[kind])
    return out


def generated_battery(module, name, spec, max_calls):
    """Type-driven calls for one function SPEC, deterministic given (module, name).

    The spec comes from the FILE's AST (`file_function_specs`), not from
    `inspect.signature` of the runtime object: the model calls the
    function the file defines, so the file's signature is the one that
    decides arity — and it is the only one available when CPython's
    runtime name is a C accelerator with no signature at all.

    ARITY VARIANTS: a parameter with a default is bound in one variant and
    omitted in another, because the model's default binding is a call-site
    merge (docs/memory-model.md §call-site keyword arguments) and the
    omitted-argument path is a different path in it.

    Returns ([[canonical arg ...] ...], skip reason or None)."""
    if spec["bad_signature"]:
        # The runner's typed-call protocol passes POSITIONAL arguments; a
        # `*args`/`**kw`/keyword-only signature is not drivable through it.
        # Loud as a skip, never silently called with fewer arguments.
        return [], "signature has %s" % spec["bad_signature"]
    probe = max(4 * max_calls, 16)   # the pool `select_battery` picks from
    params = [_Param(p) for p in spec["params"]]
    required = [p for p in params if not p.has_default]
    arities = sorted({len(required), len(params)})
    rng = random.Random(_seed_for(module, name))
    calls = []
    seen = set()
    for arity in arities:
        pools = [_pool_for(p) for p in params[:arity]]
        if any(not pool for pool in pools):
            continue
        if arity == 0:
            candidates = [()]
        else:
            # Enumerate the product deterministically when it is small, and
            # SAMPLE it with the per-function seed when it is not. Sampling
            # is over sorted index tuples, so it does not depend on dict or
            # set ordering anywhere.
            total = 1
            for pool in pools:
                total *= len(pool)
            if total <= probe * 4:
                idx = [()]
                for pool in pools:
                    idx = [t + (i,) for t in idx for i in range(len(pool))]
            else:
                idx = sorted({tuple(rng.randrange(len(p)) for p in pools)
                              for _ in range(probe * 8)})
            candidates = [tuple(pools[i][j] for i, j in enumerate(t)) for t in idx]
            rng.shuffle(candidates)
        for args in candidates:
            try:
                enc = [to_canonical_value(a) for a in args]
            except Unmappable:
                continue
            key = json.dumps(enc, sort_keys=True)
            if key in seen:
                continue
            seen.add(key)
            calls.append(enc)
            if len(calls) >= probe:
                return calls, None
    return calls, None


def _outcome_key(row):
    """What makes two oracle outcomes the SAME KIND of answer — used to
    prefer a battery of distinct answers over eight copies of one
    TypeError."""
    st = row.get("status")
    if st == "exn":
        return "exn:%s:%s" % (row.get("exn"), row.get("exnmsg"))
    return st


def _distinct_first(rows):
    """Stable: the first row of each distinct outcome, in order, then the
    rest in order. No sets in the ordering — the order IS the battery."""
    seen = []
    first, rest = [], []
    for row in rows:
        key = _outcome_key(row[2])
        if key in seen:
            rest.append(row)
        else:
            seen.append(key)
            first.append(row)
    return first + rest


def select_battery(rows, max_calls):
    """Choose the battery from the probed candidates: every doctest row,
    then generated rows alternating between calls that RETURNED and calls
    that RAISED, distinct answers first.

    BALANCE IS THE POINT. An unannotated signature makes most generated
    tuples type-incoherent, so an unbalanced battery is eight TypeErrors
    and no evidence about the value path; a model that gets the happy path
    right and the error path wrong (or the reverse) is exactly what this
    instrument is looking for, so both halves are always represented."""
    doct = [r for r in rows if r[1] == "doctest"]
    gen = [r for r in rows if r[1] != "doctest"]
    ok = _distinct_first([r for r in gen if r[2].get("status") == "ok"])
    raised = _distinct_first([r for r in gen if r[2].get("status") != "ok"])
    out = list(doct[:max_calls])
    i = j = 0
    while len(out) < max_calls and (i < len(ok) or j < len(raised)):
        if i < len(ok):
            out.append(ok[i])
            i += 1
        if len(out) < max_calls and j < len(raised):
            out.append(raised[j])
            j += 1
    return out


def doctest_battery(module, name, doc, publics):
    """Calls read off the function's own doctests.

    A doctest is the module author's own claim about the function, so it
    goes in the battery ahead of anything generated. Only the examples this
    harness can turn into a TYPED CALL are taken: one expression statement,
    a call of a public function of this module, every argument a literal.
    Anything else is skipped silently — a doctest is a bonus, and the
    generated battery is the floor."""
    if not doc:
        return []
    out = []
    for ex in doctest.DocTestParser().get_examples(doc):
        try:
            tree = ast.parse(ex.source.strip(), mode="eval")
        except SyntaxError:
            continue
        node = tree.body
        if not isinstance(node, ast.Call) or node.keywords:
            continue
        fname = None
        if isinstance(node.func, ast.Name):
            fname = node.func.id
        elif isinstance(node.func, ast.Attribute) and isinstance(node.func.value, ast.Name):
            fname = node.func.attr
        if fname != name or fname not in publics:
            continue
        try:
            args = [ast.literal_eval(a) for a in node.args]
            enc = [to_canonical_value(a) for a in args]
        except (ValueError, SyntaxError, Unmappable):
            continue
        out.append(enc)
    return out


# ---------------------------------------------------------------------------
# running
# ---------------------------------------------------------------------------

class _CallTimeout(Exception):
    """A driven call exceeded its per-call alarm. Reported as its own status
    — a timed-out oracle call is not agreement and not a divergence."""


def _alarm(seconds):
    if seconds and hasattr(signal, "SIGALRM"):
        def handler(signum, frame):
            raise _CallTimeout()
        signal.signal(signal.SIGALRM, handler)
        signal.setitimer(signal.ITIMER_REAL, seconds)


def _alarm_off():
    if hasattr(signal, "SIGALRM"):
        signal.setitimer(signal.ITIMER_REAL, 0)


def run_call(fn, enc_args, timeout):
    """One battery call. Returns the row the driver compares: the canonical
    outcome, the STDOUT it produced, and whether it MUTATED its arguments
    (deep-compared against a copy taken before the call — the model's
    typed-call protocol reports neither, so both are recorded here and
    counted as unverified rather than assumed away)."""
    args = [from_canonical_value(a) for a in enc_args]
    before = copy.deepcopy(args)
    buf = io.StringIO()
    saved, sys.stdout = sys.stdout, buf
    row = {}
    try:
        _alarm(timeout)
        try:
            v = fn(*args)
        except _CallTimeout:
            row = {"status": "oracle-timeout"}
        except Exception as e:  # runtime errors are data
            row = {"status": "exn", "exn": exception_name(e), "exnmsg": str(e)}
        except SystemExit as e:
            row = {"status": "exn", "exn": "SystemExit", "exnmsg": str(e)}
        else:
            try:
                row = {"status": "ok", "value": to_canonical_value(v)}
            except Unmappable as u:
                row = {"status": "unmappable", "type": str(u)}
        finally:
            _alarm_off()
    finally:
        sys.stdout = saved
    out = buf.getvalue()
    if out:
        row["stdout"] = out
    try:
        if args != before:
            row["mutated"] = True
    except Exception:
        row["mutated"] = "uncomparable"
    return row


def import_body(module, path):
    """Execute the module body under IMPORT semantics and return
    (module object or None, row).

    `spec_from_file_location(NAME, PATH)` + `exec_module` is the honest
    shape: it RUNS the body (unlike `import_module` on an already-loaded
    module, which would return the interpreter's own cached copy and
    compare nothing) with `__name__` bound to NAME. `sys.modules` is
    seeded before execution because a module that imports itself — or
    whose submodule imports it — must find the object being built, which
    is exactly what CPython's import machinery does."""
    import importlib.util
    buf = io.StringIO()
    saved, sys.stdout = sys.stdout, buf
    keep = sys.modules.get(module)
    try:
        spec = importlib.util.spec_from_file_location(module, path)
        if spec is None or spec.loader is None:
            return None, {"status": "oracle-error", "msg": "no import spec for %s" % path}
        mod = importlib.util.module_from_spec(spec)
        sys.modules[module] = mod
        try:
            spec.loader.exec_module(mod)
        except BaseException as e:  # an import that raises is a real outcome
            sys.modules.pop(module, None)
            if keep is not None:
                sys.modules[module] = keep
            return None, {"status": "exn", "exn": exception_name(e), "exnmsg": str(e),
                          "stdout": buf.getvalue()}
        return mod, {"status": "ok", "stdout": buf.getvalue()}
    finally:
        sys.stdout = saved


def file_function_specs(path):
    """The public functions THE FILE DEFINES, read off its AST.

    "Defined in-module" is decided statically, on the same text the model
    is shown, for two reasons the runtime cannot serve. First, a name can
    be REBOUND by the module body after the `def` — `bisect.py`'s guarded
    `from _bisect import *` replaces all four pure functions with C ones,
    so a runtime-only walk finds no in-file function in bisect at all and
    would report the module as having no public surface. Second, the model
    calls what the file defines; the file's signature is therefore the
    arity the battery must respect.

    Sorted by name — the battery's order is part of its determinism."""
    with open(path, "rb") as f:
        source = f.read()
    tree = ast.parse(source, filename=path)
    out = []
    for node in tree.body:
        if isinstance(node, ast.AsyncFunctionDef):
            out.append({"name": node.name, "params": [], "doc": None, "decorated": False,
                        "bad_signature": "async def"})
            continue
        if not isinstance(node, ast.FunctionDef) or node.name.startswith("_"):
            continue
        a = node.args
        bad = None
        if a.vararg is not None:
            bad = "*%s" % a.vararg.arg
        elif a.kwarg is not None:
            bad = "**%s" % a.kwarg.arg
        elif a.kwonlyargs:
            bad = "keyword-only parameters"
        positional = list(getattr(a, "posonlyargs", [])) + list(a.args)
        defaults = list(a.defaults)
        first_default = len(positional) - len(defaults)
        params = []
        for i, arg in enumerate(positional):
            p = {"name": arg.arg}
            if arg.annotation is not None:
                p["annotation"] = _annotation_text(arg.annotation)
            if i >= first_default:
                p["has_default"] = True
                try:
                    p["default"] = ast.literal_eval(defaults[i - first_default])
                except (ValueError, SyntaxError):
                    pass
            params.append(p)
        out.append({"name": node.name, "params": params, "doc": ast.get_docstring(node),
                    "decorated": bool(node.decorator_list), "bad_signature": bad})
    return sorted(out, key=lambda s: s["name"])


def _annotation_text(node):
    """An annotation as SOURCE TEXT — a `Name`/`Attribute`/string constant
    only. Never evaluated: evaluating an annotation runs the module's code
    in this process, and the battery only needs the head name anyway."""
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        return node.attr
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        return node.value
    if isinstance(node, ast.Subscript):
        return _annotation_text(node.value)
    return None


def resolve_runtime(mod, name, path):
    """(callable or None, implementation tag).

    The tag is what the imported module's public name actually IS after the
    body ran, and it is data the comparison needs: `python` (the file's own
    `def`, the thing the model models), `override` (something else is bound
    under this name — CPython's C accelerator after a guarded
    `from _X import *`, the standing §2.5 accelerator-equivalence
    obligation of docs/memory-model.md §import forms, which this harness is
    the differential test FOR), or `missing`."""
    fn = getattr(mod, name, None)
    if fn is None:
        return None, "missing"
    if not callable(fn):
        return None, "not-callable:%s" % type(fn).__name__
    code = getattr(fn, "__code__", None)
    if code is not None and os.path.realpath(code.co_filename) == os.path.realpath(path):
        return fn, "python"
    return fn, "override:%s" % type(fn).__name__


def main(argv=None):
    parser = argparse.ArgumentParser(prog="library_oracle.py")
    parser.add_argument("--module", required=True, help="the module's IMPORT name")
    parser.add_argument("--file", required=True)
    parser.add_argument("--out", required=True)
    parser.add_argument("--calls", action="store_true",
                        help="also enumerate and drive the public functions "
                             "(the driver passes this only once the BODY matched)")
    parser.add_argument("--max-calls", type=int, default=8)
    parser.add_argument("--call-timeout", type=float, default=5.0)
    opts = parser.parse_args(argv)

    result = {"module": opts.module, "file": opts.file, "python": sys.version.split()[0]}
    mod, body = import_body(opts.module, opts.file)
    result["body"] = body
    result["functions"] = []
    if mod is not None and opts.calls:
        specs = file_function_specs(opts.file)
        names = set(s["name"] for s in specs)
        for spec in specs:
            name = spec["name"]
            fn, impl = resolve_runtime(mod, name, opts.file)
            row = {"name": name, "impl": impl, "decorated": spec["decorated"]}
            if fn is None:
                row["skipped"] = "public name is %s after the body ran" % impl
                result["functions"].append(row)
                continue
            if UNSAFE_CALL.match(name):
                row["skipped"] = "unsafe verb (harness/library_oracle.py UNSAFE_CALL)"
                result["functions"].append(row)
                continue
            doct = doctest_battery(opts.module, name, spec["doc"], names)
            gen, skip = generated_battery(opts.module, name, spec, opts.max_calls)
            if skip and not doct:
                row["skipped"] = skip
                result["functions"].append(row)
                continue
            candidates = []
            seen = set()
            for enc, source in ([(e, "doctest") for e in doct] + [(e, "generated") for e in gen]):
                key = json.dumps(enc, sort_keys=True)
                if key in seen:
                    continue
                seen.add(key)
                candidates.append((enc, source))
            probed = [(enc, source, run_call(fn, enc, opts.call_timeout))
                      for enc, source in candidates]
            row["probed"] = len(probed)
            row["calls"] = [{"args": enc, "source": source, "oracle": oracle}
                            for enc, source, oracle in select_battery(probed, opts.max_calls)]
            result["functions"].append(row)
    with open(opts.out, "w", encoding="utf-8") as f:
        json.dump(result, f, sort_keys=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
