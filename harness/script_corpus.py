#!/usr/bin/env python3
"""leanpy v0 — the script-corpus differential mode (docs/backlog.md).

Usage (any cwd; the script re-roots itself at the repo root):

    python3 harness/script_corpus.py [--scripts harness/scripts.json]
                                     [--no-build] [--runner CMD] [--fuel N]

For every row ``{"file": ..., "expect": "match"|"unsupported"}``:

  1. re-extracts the envelope (deterministic; extractors/python/extract.py);
  2. runs the file under CPython (``sys.executable`` — the repo's pinned
     3.9 oracle) capturing stdout + exit code;
  3. runs ``lake exe leanmodels-run --script <envelope>`` capturing
     stdout + exit code;
  4. ``match``  — passes iff stdout AND exit code agree exactly;
     ``unsupported`` — passes iff the Lean side exits 3 (the LOUD leanpy
     code; a timeout, exit 4, is NOT agreement), with the blocking
     construct reported as telemetry — loudness as prioritization signal.

Completeness telemetry is the point: the summary reports the fraction of
the corpus completing and WHICH construct blocked each refusal.

Python 3.9 compatible.
"""

import argparse
import json
import os
import re
import subprocess
import sys

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


TRACEBACK_CLASS = re.compile(r"^(?:[A-Za-z_][\w.]*\.)?([A-Za-z_]\w*)(?::.*)?$")


def exc_class(stderr):
    """The exception CLASS a died run reports, read off the last traceback
    line (CPython) or off the runner's own stderr (the Lean side prints the
    class name alone). CPython maps EVERY uncaught exception to exit 1, so
    without this the comparison could not tell two exceptions apart."""
    for line in reversed((stderr or "").splitlines()):
        line = line.strip()
        if not line:
            continue
        m = TRACEBACK_CLASS.match(line)
        return m.group(1) if m else None
    return None


def run_cpython(path):
    proc = subprocess.run(
        [sys.executable, path], cwd=REPO_ROOT, capture_output=True, text=True
    )
    return proc.stdout, proc.returncode, proc.stderr


def run_lean(runner_cmd, json_path, fuel):
    cmd = list(runner_cmd) + ["--script", json_path]
    if fuel is not None:
        cmd += ["--fuel", str(fuel)]
    proc = subprocess.run(cmd, cwd=REPO_ROOT, capture_output=True, text=True)
    return proc.stdout, proc.returncode, proc.stderr.strip()


def main(argv=None):
    parser = argparse.ArgumentParser(prog="script_corpus.py")
    parser.add_argument("--scripts", default=os.path.join("harness", "scripts.json"))
    parser.add_argument("--no-build", action="store_true")
    parser.add_argument("--runner", default="lake exe leanmodels-run")
    parser.add_argument("--fuel", type=int, default=None)
    opts = parser.parse_args(argv)

    os.chdir(REPO_ROOT)
    runner_cmd = opts.runner.split()

    if not opts.no_build:
        if subprocess.run(["lake", "build"], cwd=REPO_ROOT).returncode != 0:
            print("error: `lake build` failed", file=sys.stderr)
            return 2

    with open(opts.scripts, "r", encoding="utf-8") as f:
        rows = json.load(f)

    failures = 0
    completed = 0
    blocked = []
    for row in rows:
        src = row["file"]
        expect = row.get("expect", "match")
        ext = subprocess.run(
            [sys.executable, "extractors/python/extract.py", src],
            cwd=REPO_ROOT, capture_output=True, text=True,
        )
        if ext.returncode != 0:
            print("%-42s ERROR (extractor: %s)" % (src, ext.stderr.strip()))
            failures += 1
            continue
        json_path = os.path.splitext(src)[0] + ".json"
        cout, ccode, cerr = run_cpython(src)
        lout, lcode, lerr = run_lean(runner_cmd, json_path, opts.fuel)
        if expect == "unsupported":
            if lcode == 3:
                print("%-42s LOUD    (%s)" % (src, lerr))
                blocked.append((src, lerr))
            else:
                print("%-42s MISMATCH (expected loud exit 3, got %d: %s)"
                      % (src, lcode, lerr or lout.strip()))
                failures += 1
        else:
            exc_ok = (ccode == 0 or lcode != 1
                      or exc_class(cerr) == exc_class(lerr))
            if cout == lout and ccode == lcode and exc_ok:
                print("%-42s MATCH   (exit %d, %d stdout bytes)"
                      % (src, ccode, len(cout)))
                completed += 1
            else:
                print("%-42s MISMATCH" % src)
                print("  cpython: exit %d, stdout %r" % (ccode, cout))
                print("  lean:    exit %d, stdout %r, exc %r" % (lcode, lout, exc_class(lerr)))
                if ccode:
                    print("  cpython exc: %r" % (exc_class(cerr),))
                failures += 1

    total = len(rows)
    print("-" * 72)
    print("%d scripts: %d failed, %d completed-and-matched, %d loud-blocked"
          % (total, failures, completed, len(blocked)))
    for src, msg in blocked:
        print("  blocked: %-34s %s" % (src, msg))
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
