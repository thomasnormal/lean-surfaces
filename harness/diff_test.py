#!/usr/bin/env python3
"""Differential test harness: CPython vs the Lean definitional interpreter.

Usage (any cwd; the script re-roots itself at the repo root):

    python3 harness/diff_test.py [--cases harness/cases.json] [--fuel N]
                                 [--no-build] [--runner CMD]

For every case in harness/cases.json (DESIGN.md format:
``[{"file": ..., "function": ..., "args": [[...], ...], "expect": ...}]``)
this (a case may carry ``"fuel": N`` to raise the runner's default for
its rows — deep drains like `sf_order.move_order` need it):

  1. imports the ``.py`` source by path (importlib) and calls the function,
     mapping the return value / raised exception to the canonical JSON form
     of DESIGN.md "Runner + differential harness" (ints/bools/str/None/
     list/tuple only; anything else is recorded as unmappable and can never
     match);
  2. runs the Lean side of ALL rows through ONE
     ``lake exe leanmodels-run --batch <jobs.jsonl>`` process (one job line
     per row; the runner prints one canonical JSON line per row, in order,
     flushed as produced) and pairs the stream back up with the rows;
  3. compares the two canonical forms.

The batch shape is load-bearing: one runner process per ROW paid the
`lake` startup (a full replay of the build graph) 615 times over —
hours of redundant work. One process pays it once. Progress is printed
to stderr per row as runner lines arrive, so there is never a silent
multi-minute stretch.

``"expect": "match"`` requires equality; ``"expect": "unsupported"``
whitelists a documented v0 semantic-tier gap — the case passes iff the Lean
side reports ``{"status": "unsupported"}`` (CPython's answer is shown for
information only).

A case may carry ``"clock"`` (docs/memory-model.md §the trace clock):
either a list of ints — BOTH sides replay it — or ``"record"`` — the
CPython side's stub reads the real clock as integer microseconds,
records, and the model replays the recorded list. The stub is bound to
the module's ``time`` name per row and restored; a CPython-side underrun
raises ``ClockTraceUnderrun`` (distinctively named — never a match).
Rows without ``"clock"`` run with the empty trace, exactly as before.

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


def _reexec_under_pinned_cpython():
    """RUN THE ORACLE ON THE PINNED INTERPRETER (2026-08-13 fix).

    This harness imports each `.py` IN-PROCESS and calls the function, so
    its oracle is whatever Python launched it — on this machine 3.14,
    while the model's tier is specified against CPython 3.9
    (docs/backlog.md). Every one of the 998 cases was therefore compared
    against the wrong reference: a genuine 3.9 divergence could hide and a
    3.14-only behaviour could be reported as a model bug. Re-exec into the
    pin instead of silently measuring the wrong thing; if the pin is not
    installed, say so LOUDLY and keep going, never quietly.

    `LEANPY_CPYTHON=…` overrides; `LEANPY_NO_REEXEC=1` disables (the
    re-exec sets it, so this runs at most once).
    """
    if os.environ.get("LEANPY_NO_REEXEC"):
        return
    want = os.environ.get("LEANPY_CPYTHON") or "python3.9"
    if sys.version_info[:2] == (3, 9) and not os.environ.get("LEANPY_CPYTHON"):
        return
    from shutil import which
    exe = which(want)
    if exe is None:
        print("harness/diff_test.py: WARNING the pinned oracle %r is not installed; "
              "comparing against %s instead — version drift will read as model divergence"
              % (want, sys.version.split()[0]), file=sys.stderr)
        return
    if os.path.realpath(exe) == os.path.realpath(sys.executable):
        return
    os.environ["LEANPY_NO_REEXEC"] = "1"
    os.execv(exe, [exe, os.path.abspath(__file__)] + sys.argv[1:])


_reexec_under_pinned_cpython()


class Unmappable(Exception):
    """A CPython value outside the canonical set (e.g. float)."""


class ClockTraceUnderrun(Exception):
    """The CPython side's replayed clock trace ran out (record-replay,
    docs/memory-model.md §the trace clock). Distinctively named so the
    canonicalized exception can never accidentally match a model row."""


class _ReplayClock(object):
    """A stub bound to the module's `time` name: `.time()` pops the next
    reading of a fixed trace. Underrun raises ClockTraceUnderrun — loud,
    never a silent 0 (the model side refuses with `unsupported`)."""

    def __init__(self, readings):
        self._readings = list(readings)

    def time(self):
        if not self._readings:
            raise ClockTraceUnderrun()
        return self._readings.pop(0)


class _RecordingClock(object):
    """A stub bound to the module's `time` name: `.time()` reads the REAL
    clock as INTEGER MICROSECONDS (`time.time_ns() // 1000` — an int, the
    recorded representation decision: the oracle run CONSUMES exactly what
    it records, so the model's replay sees literally the same integers)."""

    def __init__(self):
        self.readings = []

    def time(self):
        import time as _time
        r = _time.time_ns() // 1000
        self.readings.append(r)
        return r


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


def from_typed(a):
    """A cases.json argument: a plain int, or a canonical typed value
    ({"t": ..., "v": ...} — the runner's own encoding) for
    list/tuple/str/bool/None arguments. Returns the Python value."""
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
        return [from_typed(x) for x in a["v"]]
    if t == "tuple":
        return tuple(from_typed(x) for x in a["v"])
    raise ValueError("bad typed argument: %r" % (a,))


def batch_job(json_path, fname, args, fuel, clock=None):
    """One jobs-file line for `leanmodels-run --batch` (compact JSON).
    cases.json argument encoding is already the runner's own: plain ints
    stay JSON numbers, typed values ride unchanged. `clock` (a list of
    ints) seeds the model world's clock trace — the replay half of the
    record-replay protocol (docs/memory-model.md §the trace clock)."""
    job = {"path": json_path, "function": fname, "args": args}
    if fuel is not None:
        job["fuel"] = fuel
    if clock is not None:
        job["clock"] = list(clock)
    return json.dumps(job, separators=(",", ":"))


def load_module(path):
    """Import a Python source file by path (fresh, not via sys.path)."""
    name = "diffcase_" + os.path.splitext(os.path.basename(path))[0]
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot import %s" % path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def run_cpython_clock(mod, fname, args, clock_spec):
    """The CPython half of record-replay (docs/memory-model.md §the trace
    clock): bind the module's `time` name to a stub for the duration of
    ONE row, run, and return (result, trace) where `trace` is the exact
    integer trace the MODEL must replay. `clock_spec` is either a list of
    ints (both sides replay it) or "record" (the stub reads the real
    clock as integer microseconds and records — the oracle CONSUMES what
    it records, so both sides see the same integers)."""
    if clock_spec == "record":
        stub = _RecordingClock()
    elif isinstance(clock_spec, list):
        stub = _ReplayClock(clock_spec)
    else:
        raise ValueError('"clock" must be "record" or a list of ints: %r'
                         % (clock_spec,))
    had = hasattr(mod, "time")
    saved = getattr(mod, "time", None)
    mod.time = stub
    try:
        result = run_cpython(mod, fname, args)
    finally:
        if had:
            mod.time = saved
        else:
            delattr(mod, "time")
    trace = stub.readings if clock_spec == "record" else list(clock_spec)
    return result, trace


def run_cpython(mod, fname, args):
    """Call mod.fname(*args); canonicalize the outcome."""
    fn = getattr(mod, fname, None)
    if fn is None:
        return {"status": "harness-error", "msg": "no function %r" % fname}
    try:
        v = fn(*[from_typed(a) for a in args])
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


def run_lean_batch(runner_cmd, jobs, on_result):
    """Run ALL jobs through one `--batch` runner process.

    ``jobs`` is a list of jobs-file lines (`batch_job`; fuel rides on the
    job). Streams the runner's stdout: only lines starting with ``{`` are
    results (anything else — e.g. `lake` replay chatter — is echoed to
    stderr); calls ``on_result(i, result)`` as result ``i`` lands so the
    caller can record it and print progress. A runner that dies early
    yields explicit ``runner-error`` entries for the missing tail, never
    a silently shortened table."""
    jobs_path = os.path.join(REPO_ROOT, "harness", ".batch_jobs.jsonl")
    with open(jobs_path, "w", encoding="utf-8") as f:
        f.write("\n".join(jobs) + "\n")
    cmd = list(runner_cmd) + ["--batch", jobs_path]
    n = 0
    try:
        proc = subprocess.Popen(
            cmd, cwd=REPO_ROOT, stdout=subprocess.PIPE, text=True
        )
        for line in proc.stdout:
            line = line.strip()
            if not line:
                continue
            if not line.startswith("{"):
                print("runner: %s" % line, file=sys.stderr)
                continue
            try:
                result = json.loads(line)
            except ValueError as e:
                result = {"status": "runner-error",
                          "msg": "bad JSON: %s (%r)" % (e, line)}
            if n >= len(jobs):
                raise RuntimeError(
                    "runner printed more results than the %d jobs — the "
                    "pairing is broken, refusing to guess" % len(jobs))
            on_result(n, result)
            n += 1
        proc.wait()
        while n < len(jobs):
            on_result(n, {
                "status": "runner-error",
                "msg": "runner exited (code %d) after %d/%d results"
                       % (proc.returncode, n, len(jobs)),
            })
            n += 1
    finally:
        os.unlink(jobs_path)


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
    parser.add_argument(
        "--monadic", action="store_true", help='target the MONADIC REBUILD (LeanModels/Python/Monadic/) instead of the trunk interpreter - appends --monadic to the runner command. The acceptance gate is parity with the trunk on this same corpus.',
    )
    opts = parser.parse_args(argv)

    os.chdir(REPO_ROOT)
    runner_cmd = opts.runner.split()
    if opts.monadic:
        runner_cmd = runner_cmd + ["--monadic"]

    if not opts.no_build:
        build = subprocess.run(["lake", "build"], cwd=REPO_ROOT)
        if build.returncode != 0:
            print("error: `lake build` failed (exit %d)" % build.returncode,
                  file=sys.stderr)
            return 2

    with open(opts.cases, "r", encoding="utf-8") as f:
        cases = json.load(f)

    # Pass 1: CPython side of every row, plus its batch job line.
    calls = []    # (call_repr, expect, cpy_result)
    jobs = []
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
        fuel = case.get("fuel", opts.fuel)
        clock_spec = case.get("clock")
        for args in case["args"]:
            call = "%s(%s)" % (fname,
                               ", ".join(repr(from_typed(a)) for a in args))
            if clock_spec is None:
                cpy, trace = run_cpython(mod, fname, args), None
            else:
                cpy, trace = run_cpython_clock(mod, fname, args, clock_spec)
            calls.append((call, expect, cpy))
            jobs.append(batch_job(json_path, fname, args, fuel, trace))

    # Pass 2: the Lean side — ONE runner process for all rows, verdicts
    # streamed to stderr as they land.
    rows = []
    failures = 0
    whitelisted = 0

    def on_result(i, lean):
        nonlocal failures, whitelisted
        call, expect, cpy = calls[i]
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
        rows.append((call, pretty(cpy), pretty(lean), verdict))
        print("[%d/%d] %-10s %s" % (i + 1, len(jobs), verdict, call),
              file=sys.stderr)

    run_lean_batch(runner_cmd, jobs, on_result)

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
    print("oracle: Python %s (the model's tier is specified against 3.9)"
          % (sys.version.split()[0],))
    print("interpreter: %s"
          % ("MONADIC REBUILD (LeanModels/Python/Monadic/)" if opts.monadic
             else "trunk (LeanModels/Python/Semantics.lean)"))
    print("%d cases: %d failed, %d whitelisted-unsupported, %d matched"
          % (len(rows), failures, whitelisted,
             len(rows) - failures - whitelisted))
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
