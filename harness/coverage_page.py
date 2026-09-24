#!/usr/bin/env python3
"""coverage_page.py — generate docs/python-coverage.md from measurements.

    python3 harness/coverage_page.py [--runner CMD] [--out PATH] [--check]

Every number on the page is produced by a run, never typed by hand:

* the DIFFERENTIAL PASS RATE is `harness/diff_test.py`'s own summary line
  (every row of `harness/cases.json`, model vs the pinned CPython oracle);
* the GRAMMAR TABLE is `harness/refusal_census.py --grammar` (one witness
  program per CPython 3.9 `ast` production, run through both), verdict and
  refusal message per row;
* the BUILTIN TABLES are read from the two name tables in
  `LeanModels/Python/Ast.lean` (`isBuiltinName`: the names the interpreter
  dispatches; `isPyBuiltinName`: every name CPython 3.9 binds). A name in
  the second and not the first refuses loudly when used.

`--check` regenerates the page and exits 1 if it differs from the committed
file, so a change to the tier that moves coverage must also move the page.
The runner is never built here (`--runner` must point at a built
`leanmodels-run`; the default is the lake build product).

Python 3.9 compatible.
"""

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DEFAULT_RUNNER = os.path.join(".lake", "build", "bin", "leanmodels-run")
DEFAULT_OUT = os.path.join("docs", "python-coverage.md")
AST_LEAN = os.path.join("LeanModels", "Python", "Ast.lean")
PINNED_ORACLE = "CPython 3.9"

sys.path.insert(0, os.path.join(REPO_ROOT, "harness"))


def lean_def_body(src, name):
    """The text of `def <name> …` up to the next top-level declaration."""
    m = re.search(r"^def %s\b.*?(?=^(?:def|/--|/-!|end|theorem|inductive)\b)"
                  % re.escape(name), src, re.S | re.M)
    if not m:
        raise SystemExit("coverage_page: cannot find `def %s` in %s"
                         % (name, AST_LEAN))
    # Drop line comments: they quote names that are not table members.
    return re.sub(r"--[^\n]*", "", m.group(0))


def builtin_tables():
    with open(os.path.join(REPO_ROOT, AST_LEAN), encoding="utf-8") as f:
        src = f.read()
    modelled = set(re.findall(r'id == "([^"]+)"',
                              lean_def_body(src, "isBuiltinName")))
    cpython = set(re.findall(r'"([^"]+)"',
                             lean_def_body(src, "isPyBuiltinName")))
    catches = set(re.findall(r'^\s*\|\s*"([A-Za-z]+)"\s*,',
                             lean_def_body(src, "builtinExcCatches"), re.M))
    if not modelled or not cpython or not catches:
        raise SystemExit("coverage_page: a builtin table parsed empty")
    stray = sorted(modelled - cpython - {"count"})
    if stray:
        raise SystemExit("coverage_page: modelled names CPython does not "
                         "bind: %s" % ", ".join(stray))
    return modelled, cpython, catches


def run(cmd, env=None):
    proc = subprocess.run(cmd, cwd=REPO_ROOT, capture_output=True, text=True,
                          env=env)
    return proc.returncode, proc.stdout, proc.stderr


def diff_summary(runner):
    rc, out, err = run([sys.executable, "harness/diff_test.py", "--no-build",
                        "--runner", runner])
    summ = [l for l in out.splitlines() if re.match(r"\d+ cases: ", l)]
    oracle = [l for l in out.splitlines() if l.startswith("oracle: ")]
    if not summ:
        raise SystemExit("coverage_page: diff_test.py printed no summary "
                         "(exit %d)\n%s" % (rc, (out + err)[-2000:]))
    m = re.match(r"(\d+) cases: (\d+) failed, (\d+) whitelisted-unsupported, "
                 r"(\d+) matched", summ[-1])
    cases, failed, white, matched = (int(x) for x in m.groups())
    return {"cases": cases, "failed": failed, "whitelisted": white,
            "matched": matched,
            "oracle": oracle_minor(oracle[-1] if oracle else "")}


def oracle_minor(line):
    """`CPython 3.9`, not `3.9.25`: the patch release differs between hosts
    and must not make `--check` fail. The tier is specified against 3.9."""
    m = re.search(r"Python (\d+\.\d+)", line)
    if not m:
        raise SystemExit("coverage_page: diff_test.py printed no oracle "
                         "version")
    return "CPython " + m.group(1)


def grammar_rows(runner):
    import refusal_census
    fd, path = tempfile.mkstemp(suffix=".json")
    os.close(fd)
    try:
        rc, out, err = run([sys.executable, "harness/refusal_census.py",
                            "--grammar", "--no-build", "--runner", runner,
                            "--json", path])
        with open(path, encoding="utf-8") as f:
            rows = json.load(f)["grammar"]
    finally:
        os.unlink(path)
    if not rows:
        raise SystemExit("coverage_page: grammar census produced no rows "
                         "(exit %d)\n%s" % (rc, (out + err)[-2000:]))
    notes = {w["id"]: w["note"] for w in refusal_census.W}
    for r in rows:
        r["note"] = notes.get(r["id"], "")
    return rows


def cell(s, n=110):
    s = " ".join(s.split()).replace("|", "\\|")
    return s if len(s) <= n else s[:n - 1] + "…"


def render(diff, grammar, tables):
    modelled, cpython, catches = tables
    funcs = sorted(n for n in cpython if n[:1].islower())
    consts = {"True", "False", "None"}
    L = []
    L.append("# Python coverage")
    L.append("")
    L.append("<!-- GENERATED by harness/coverage_page.py — do not edit. "
             "Regenerate: python3 harness/coverage_page.py -->")
    L.append("")
    L.append("What the Lean model of Python runs, measured. Everything outside "
             "the modelled tier is **refused loudly** (`Res.unsupported`, with "
             "a message naming the construct); it is never answered with a "
             "wrong value. The pass rate and the grammar table come from runs "
             "against the pinned CPython oracle; the builtin lists are the "
             "interpreter's own name tables. CI fails if this page goes stale "
             "(`harness/coverage_page.py --check`).")
    L.append("")
    L.append("## Differential pass rate")
    L.append("")
    decided = diff["cases"] - diff["whitelisted"]
    L.append("`harness/diff_test.py` runs every row of `harness/cases.json` "
             "through the model and through %s and compares the outcome "
             "(value, or exception class) exactly." % diff["oracle"])
    L.append("")
    L.append("| rows | agree with CPython | disagree | recorded refusals |")
    L.append("|---:|---:|---:|---:|")
    L.append("| %d | %d | %d | %d |" % (diff["cases"], diff["matched"],
                                        diff["failed"], diff["whitelisted"]))
    L.append("")
    L.append("Of the %d rows the model decides, %d agree with CPython "
             "(%.1f%%). A *recorded refusal* is a row kept in the suite to pin "
             "a known gap: the model must refuse it, and the suite fails if it "
             "ever answers instead." % (
                 decided, diff["matched"],
                 100.0 * diff["matched"] / decided if decided else 0.0))
    L.append("")
    L.append("## Grammar")
    L.append("")
    n = len(grammar)
    cnt = {}
    for r in grammar:
        cnt[r["verdict"]] = cnt.get(r["verdict"], 0) + 1
    L.append("`harness/refusal_census.py --grammar`: one small witness program "
             "per production of CPython 3.9's `ast` grammar, plus edge rows. "
             "MATCH means the model ran the witness and agreed with CPython; "
             "it does not mean every use of the construct is in tier "
             "(`2 * 3` runs, `\"ab\" * 3` may refuse). REFUSE shows the "
             "model's refusal message.")
    L.append("")
    L.append("%d witnesses: %s." % (n, ", ".join(
        "%d %s" % (cnt[k], k) for k in sorted(cnt, key=lambda k: -cnt[k]))))
    groups = []
    for r in grammar:
        g = r["id"].split(".")[0]
        if g not in groups:
            groups.append(g)
    for g in groups:
        L.append("")
        L.append("### `%s`" % g)
        L.append("")
        L.append("| witness | verdict | refusal message / note |")
        L.append("|---|---|---|")
        for r in grammar:
            if r["id"].split(".")[0] != g:
                continue
            detail = r["detail"] if r["verdict"] != "MATCH" else r["note"]
            L.append("| `%s` | %s | %s |" % (r["id"][len(g) + 1:] or g,
                                            r["verdict"], cell(detail)))
    L.append("")
    L.append("## Builtins")
    L.append("")
    L.append("Read from `LeanModels/Python/Ast.lean`. A modelled name may "
             "still refuse some argument shapes (see the grammar and the "
             "differential suite); a refused name always refuses, and never "
             "raises a fabricated `NameError`.")
    L.append("")
    fm = [f for f in funcs if f in modelled]
    fr = [f for f in funcs if f not in modelled]
    L.append("**Modelled functions (%d of %d):** %s" % (
        len(fm), len(funcs), ", ".join("`%s`" % f for f in fm)))
    L.append("")
    L.append("**Refused functions (%d):** %s" % (
        len(fr), ", ".join("`%s`" % f for f in fr)))
    L.append("")
    L.append("Also modelled: `count` (from `from itertools import count`).")
    L.append("")
    exc = sorted(catches)
    L.append("**Exception classes `except` can name (%d):** %s. Other "
             "exception names refuse, including ancestors such as `LookupError`; "
             "user classes `class E(Exception): pass` are admitted." % (len(exc), ", ".join("`%s`" % e for e in exc)))
    L.append("")
    others = sorted(n for n in cpython
                    if not n[:1].islower() and n not in catches
                    and n not in consts)
    L.append("**Other CPython builtin names (%d)**, refused when used: %s." % (
        len(others), ", ".join("`%s`" % o for o in others)))
    L.append("")
    return "\n".join(L)


def main(argv=None):
    p = argparse.ArgumentParser(prog="coverage_page.py")
    p.add_argument("--runner", default=DEFAULT_RUNNER)
    p.add_argument("--out", default=DEFAULT_OUT)
    p.add_argument("--check", action="store_true",
                   help="exit 1 if the committed page is stale")
    opts = p.parse_args(argv)
    os.chdir(REPO_ROOT)
    runner = opts.runner
    if not os.path.exists(runner.split()[0]) and " " not in runner:
        print("coverage_page: runner %r not built (lake build leanmodels-run)"
              % runner, file=sys.stderr)
        return 2
    diff = diff_summary(runner)
    if diff["oracle"] != PINNED_ORACLE:
        # A page measured against another CPython is not the page; say so
        # instead of reporting it as mere staleness.
        print("coverage_page: the oracle is %s, but the tier and this page "
              "are pinned to %s — install python3.9 (or set LEANPY_CPYTHON)"
              % (diff["oracle"], PINNED_ORACLE), file=sys.stderr)
        return 2
    page = render(diff, grammar_rows(runner), builtin_tables())
    if opts.check:
        try:
            with open(opts.out, encoding="utf-8") as f:
                old = f.read()
        except OSError:
            old = ""
        if old != page:
            print("coverage_page: %s is STALE — regenerate with "
                  "`python3 harness/coverage_page.py` and commit it"
                  % opts.out, file=sys.stderr)
            return 1
        print("coverage_page: %s is fresh" % opts.out)
        return 0
    with open(opts.out, "w", encoding="utf-8") as f:
        f.write(page)
    print("coverage_page: wrote %s" % opts.out)
    return 0


if __name__ == "__main__":
    sys.exit(main())
