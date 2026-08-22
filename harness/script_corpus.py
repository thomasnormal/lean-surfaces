#!/usr/bin/env python3
"""leanpy v0 — the script-corpus differential mode (docs/backlog.md).

Usage (any cwd; the script re-roots itself at the repo root):

    python3 harness/script_corpus.py [--scripts harness/scripts.json]
                                     [--no-build] [--runner CMD] [--fuel N]

For every row ``{"file": ..., "expect": "match"|"unsupported"}``:

  1. re-extracts the envelope (deterministic; extractors/python/extract.py)
     into the shared leanpy CACHE — never beside the source, which used to
     rewrite tracked envelopes on every run;
  2. runs the file under CPython (the pinned 3.9 oracle, ``default_oracle``)
     capturing stdout + exit code;
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
import importlib.machinery
import importlib.util
import json
import os
import re
import subprocess
import sys

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def _reexec_under_pinned_frontend():
    """RUN THE FRONTEND ON THE PINNED INTERPRETER (2026-08-15 fix).

    The ORACLE here has been pinned since 2026-08-13 (`default_oracle`
    below). The FRONTEND was not: extraction ran under `sys.executable`,
    so `python3 harness/script_corpus.py` parsed the corpus with whatever
    python3 the box has — 3.14 on this laptop — while comparing against a
    3.9 oracle. Same fix, same knobs, as `harness/leanpy_survey.py`:
    `LEANPY_FRONTEND` overrides, `LEANPY_NO_REEXEC=1` disables, and a
    missing pin WARNS LOUDLY and keeps going.
    """
    if os.environ.get("LEANPY_NO_REEXEC"):
        return
    want = os.environ.get("LEANPY_FRONTEND") or "python3.9"
    if sys.version_info[:2] == (3, 9) and not os.environ.get("LEANPY_FRONTEND"):
        return
    from shutil import which
    exe = which(want)
    if exe is None:
        print("harness/script_corpus.py: WARNING the pinned frontend %r is not "
              "installed; extracting with %s instead — the model may be shown a "
              "different program than the oracle runs"
              % (want, sys.version.split()[0]), file=sys.stderr)
        return
    if os.path.realpath(exe) == os.path.realpath(sys.executable):
        return
    os.environ["LEANPY_NO_REEXEC"] = "1"
    os.execv(exe, [exe, os.path.abspath(__file__)] + sys.argv[1:])


_reexec_under_pinned_frontend()

# tools/leanpy owns the ONE extraction path (cache-keyed by source,
# extractor and frontend family). Using it here is not a tidy-up: this
# harness used to run the extractor WITHOUT `--out`, which writes the
# envelope next to the source — so a routine corpus run rewrote 44 tracked
# `harness/scripts/*.json` files in place, under whatever interpreter
# launched it. Measured 2026-08-15: a full run left them all modified with
# nothing changed but `"version": "3.9.25"` -> `"3.14.5"`.
_path = os.path.join(REPO_ROOT, "tools", "leanpy")
_spec = importlib.util.spec_from_loader(
    "leanpy", importlib.machinery.SourceFileLoader("leanpy", _path))
leanpy = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(leanpy)


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


def exc_line(stderr):
    """The last non-empty stderr line: CPython's `ClassName: message`, or
    the runner's own class(+message) line."""
    for line in reversed((stderr or "").splitlines()):
        line = line.strip()
        if line:
            return line
    return None


def default_oracle():
    """The PINNED reference interpreter (2026-08-13 fix). This corpus ran
    against `sys.executable` — whatever Python happened to launch the
    harness, which on this machine is 3.14 — while the model's tier is
    specified against CPython 3.9 (docs/backlog.md) and
    `harness/leanpy_survey.py` has always pinned it. Every "MATCH" was
    therefore measured against the wrong reference, and a real 3.9
    divergence or a fake 3.14 one could have appeared at any time; the
    exception-MESSAGE comparison added the same day is what made it
    visible (3.13+ appends `Did you mean: …?` to a NameError). The oracle
    is printed with every run for the same reason the survey prints it."""
    for cand in ("python3.9", "python3"):
        try:
            if subprocess.run([cand, "-c", ""], capture_output=True).returncode == 0:
                return cand
        except OSError:
            continue
    return sys.executable


ORACLE = os.environ.get("LEANPY_CPYTHON") or default_oracle()


def run_cpython(path):
    proc = subprocess.run(
        [ORACLE, path], cwd=REPO_ROOT, capture_output=True, text=True
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

    # THE AMENDMENT 14 CONTRACT (tools/triad.sh 4d32526): the TENURE builds the
    # runner and exports LS_RUNNER_PREBUILT=1. A gate must never build the tree
    # — it defeats --build-target narrowing and surfaces an unrelated build
    # failure as a GATE failure, attributing the number to the wrong thing
    # (§5.4a). Unset, build ONLY the runner.
    if not opts.no_build and not os.environ.get("LS_RUNNER_PREBUILT"):
        if subprocess.run(["lake", "build", "leanmodels-run"], cwd=REPO_ROOT).returncode != 0:
            print("error: `lake build` failed", file=sys.stderr)
            return 2

    cache = leanpy.default_cache()
    os.makedirs(cache, exist_ok=True)

    with open(opts.scripts, "r", encoding="utf-8") as f:
        rows = json.load(f)

    failures = 0
    completed = 0
    blocked = []
    for row in rows:
        src = row["file"]
        expect = row.get("expect", "match")
        json_path = leanpy.envelope_for(src, cache)
        if json_path is None:
            print("%-42s ERROR (extractor refused; see stderr above)" % src)
            failures += 1
            continue
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
            # The exception CLASS must always agree; the full
            # `Class: message` LINE must agree too whenever the model
            # carries a message at all (2026-08-13). A model line with no
            # colon means the `PyErr` constructor is payload-free — a
            # recorded gap, not a mismatch, so it is not compared.
            lline = exc_line(lerr)
            exc_ok = (ccode == 0 or lcode != 1
                      or (exc_class(cerr) == exc_class(lerr)
                          and (": " not in (lline or "")
                               or lline == exc_line(cerr))))
            if cout == lout and ccode == lcode and exc_ok:
                print("%-42s MATCH   (exit %d, %d stdout bytes)"
                      % (src, ccode, len(cout)))
                completed += 1
            else:
                print("%-42s MISMATCH" % src)
                print("  cpython: exit %d, stdout %r" % (ccode, cout))
                print("  lean:    exit %d, stdout %r, exc %r" % (lcode, lout, exc_line(lerr)))
                if ccode:
                    print("  cpython exc: %r" % (exc_line(cerr),))
                failures += 1

    total = len(rows)
    print("-" * 72)
    ver = subprocess.run([ORACLE, "-V"], capture_output=True, text=True)
    print("oracle: %s" % ((ver.stdout or ver.stderr).strip(),))
    print("interpreter: LeanModels/Python/Monadic/ (the only one)")
    print("%d scripts: %d failed, %d completed-and-matched, %d loud-blocked"
          % (total, failures, completed, len(blocked)))
    for src, msg in blocked:
        print("  blocked: %-34s %s" % (src, msg))
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
