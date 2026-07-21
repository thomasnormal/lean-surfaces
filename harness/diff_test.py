#!/usr/bin/env python3
"""Differential test harness: CPython vs the Lean definitional interpreter.

Usage (any cwd; the script re-roots itself at the repo root):

    python3 harness/diff_test.py [--cases harness/cases.json] [--fuel N]
                                 [--no-build] [--runner CMD]

For every case in harness/cases.json (DESIGN.md format:
``[{"file": ..., "function": ..., "args": [[...], ...], "expect": ...}]``)
this:

  1. imports the ``.py`` source by path (importlib) and calls the function,
     mapping the return value / raised exception to the canonical JSON form
     of DESIGN.md "Runner + differential harness" (ints/bools/str/None/
     list/tuple only; anything else is recorded as unmappable and can never
     match);
  2. runs ``lake exe leanmodels-run <file.json> <function> <args...>`` on the
     envelope JSON sitting next to the source and parses its single stdout
     line;
  3. compares the two canonical forms.

``"expect": "match"`` requires equality; ``"expect": "unsupported"``
whitelists a documented v0 semantic-tier gap — the case passes iff the Lean
side reports ``{"status": "unsupported"}`` (CPython's answer is shown for
information only).

Prints a result table and exits non-zero on any non-whitelisted mismatch
(and on harness-level errors such as a failing build). ``lake build`` is run
once up front so ``lake exe`` does not rebuild per case.

Python 3.9 compatible.
"""

import argparse
import importlib.util
import json
import os
import subprocess
import sys

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


class Unmappable(Exception):
    """A CPython value outside the canonical set (e.g. float)."""


def to_canonical_value(v):
    """Python value -> canonical V form (see DESIGN.md). bool before int:
    bool is an int subtype."""
    if isinstance(v, bool):
        return {"t": "bool", "v": v}
    if isinstance(v, int):
        return {"t": "int", "v": str(v)}
    if isinstance(v, str):
        return {"t": "str", "v": v}
    if v is None:
        return {"t": "none"}
    if isinstance(v, list):
        return {"t": "list", "v": [to_canonical_value(x) for x in v]}
    if isinstance(v, tuple):
        return {"t": "tuple", "v": [to_canonical_value(x) for x in v]}
    raise Unmappable(type(v).__name__)


def load_module(path):
    """Import a Python source file by path (fresh, not via sys.path)."""
    name = "diffcase_" + os.path.splitext(os.path.basename(path))[0]
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot import %s" % path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def run_cpython(mod, fname, args):
    """Call mod.fname(*args); canonicalize the outcome."""
    fn = getattr(mod, fname, None)
    if fn is None:
        return {"status": "harness-error", "msg": "no function %r" % fname}
    try:
        v = fn(*args)
    except Exception as e:  # runtime errors are data, not harness failures
        name = type(e).__name__
        # UnboundLocalError is a NameError subclass; the interpreter reports
        # the parent class (DESIGN.md name-resolution row).
        if name == "UnboundLocalError":
            name = "NameError"
        return {"status": "exn", "exn": name}
    try:
        return {"status": "ok", "value": to_canonical_value(v)}
    except Unmappable as u:
        return {"status": "unmappable", "type": str(u)}


def run_lean(runner_cmd, json_path, fname, args, fuel):
    """Run the Lean runner; parse its single canonical stdout line."""
    cmd = list(runner_cmd) + [json_path, fname] + [str(a) for a in args]
    if fuel is not None:
        cmd += ["--fuel", str(fuel)]
    proc = subprocess.run(
        cmd, cwd=REPO_ROOT, capture_output=True, text=True
    )
    if proc.returncode != 0:
        return {
            "status": "runner-error",
            "msg": "exit %d: %s" % (proc.returncode, proc.stderr.strip()),
        }
    lines = [ln for ln in proc.stdout.splitlines() if ln.strip()]
    if not lines:
        return {"status": "runner-error", "msg": "no output"}
    try:
        return json.loads(lines[-1])
    except ValueError as e:
        return {"status": "runner-error", "msg": "bad JSON: %s (%r)" % (e, lines[-1])}


def pretty_value(v):
    t = v.get("t")
    if t == "none":
        return "None"
    if t == "bool":
        return "True" if v["v"] else "False"
    if t == "int":
        return v["v"]
    if t == "str":
        return repr(v["v"])
    if t in ("list", "tuple"):
        inner = ", ".join(pretty_value(x) for x in v["v"])
        if t == "tuple":
            return "(%s%s)" % (inner, "," if len(v["v"]) == 1 else "")
        return "[%s]" % inner
    return json.dumps(v)


def pretty(result):
    status = result.get("status")
    if status == "ok":
        return "ok: " + pretty_value(result["value"])
    if status == "exn":
        return "exn: " + result["exn"]
    if status == "timeout":
        return "timeout"
    if status == "unsupported":
        return "unsupported"
    if status == "unmappable":
        return "ok: <unmappable %s>" % result.get("type")
    return "%s: %s" % (status, result.get("msg", ""))


def main(argv=None):
    parser = argparse.ArgumentParser(
        prog="diff_test.py",
        description="Differential tests: CPython vs `lake exe leanmodels-run`.",
    )
    parser.add_argument("--cases", default=os.path.join("harness", "cases.json"))
    parser.add_argument(
        "--fuel", type=int, default=None,
        help="pass --fuel N to the runner (default: runner default, 10000)",
    )
    parser.add_argument(
        "--no-build", action="store_true", help="skip the up-front `lake build`"
    )
    parser.add_argument(
        "--runner", default="lake exe leanmodels-run",
        help="runner command (default: %(default)r)",
    )
    opts = parser.parse_args(argv)

    os.chdir(REPO_ROOT)
    runner_cmd = opts.runner.split()

    if not opts.no_build:
        build = subprocess.run(["lake", "build"], cwd=REPO_ROOT)
        if build.returncode != 0:
            print("error: `lake build` failed (exit %d)" % build.returncode,
                  file=sys.stderr)
            return 2

    with open(opts.cases, "r", encoding="utf-8") as f:
        cases = json.load(f)

    rows = []
    failures = 0
    whitelisted = 0
    for case in cases:
        src = case["file"]
        fname = case["function"]
        expect = case.get("expect", "match")
        json_path = os.path.splitext(src)[0] + ".json"
        try:
            mod = load_module(src)
        except Exception as e:
            print("error: cannot import %s: %s" % (src, e), file=sys.stderr)
            return 2
        for args in case["args"]:
            cpy = run_cpython(mod, fname, args)
            lean = run_lean(runner_cmd, json_path, fname, args, opts.fuel)
            if expect == "unsupported":
                if lean.get("status") == "unsupported":
                    verdict = "WHITELISTED"
                    whitelisted += 1
                else:
                    verdict = "MISMATCH (expected unsupported)"
                    failures += 1
            else:
                if cpy.get("status") in ("harness-error",) or \
                   lean.get("status") in ("runner-error",):
                    verdict = "ERROR"
                    failures += 1
                elif cpy == lean:
                    verdict = "MATCH"
                else:
                    verdict = "MISMATCH"
                    failures += 1
            call = "%s(%s)" % (fname, ", ".join(str(a) for a in args))
            rows.append((call, pretty(cpy), pretty(lean), verdict))

    widths = [
        max(len(r[i]) for r in rows + [("case", "cpython", "lean", "verdict")])
        for i in range(4)
    ]
    fmt = "  ".join("%%-%ds" % w for w in widths)
    header = fmt % ("case", "cpython", "lean", "verdict")
    print(header)
    print("-" * len(header))
    for r in rows:
        print(fmt % r)
    print("-" * len(header))
    print("%d cases: %d failed, %d whitelisted-unsupported, %d matched"
          % (len(rows), failures, whitelisted,
             len(rows) - failures - whitelisted))
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
