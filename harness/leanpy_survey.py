#!/usr/bin/env python3
"""leanpy_survey.py — completeness as a MEASURED NUMBER.

    python3 harness/leanpy_survey.py [--corpus harness/leanpy_corpus.json]
                                     [PATH_OR_GLOB ...]
                                     [--fuel N] [--no-cpython] [--json OUT]
                                     [--cpython python3.9] [--limit N]
                                     [--batch-timeout S] [--cpython-timeout S]

Point it at arbitrary Python files (a corpus file of named groups, or
paths/globs on the command line) and it answers, for each file, which of
five things happened:

  MATCH     the model ran the whole program and its stdout AND exit code
            equal CPython's — the differential passed
  DIVERGE   the model ran the program and DISAGREED — a bug, the only
            category that fails the run (exit 1)
  REFUSE    the model refused loudly (exit 3): the construct that stopped
            it is the telemetry this survey exists to collect
  TIMEOUT   fuel exhausted (exit 4) — loud, never agreement
  ORACLE    CPython itself could not run the file (crash before compare,
            oracle timeout) — excluded from the denominator, reported

plus EXTRACT for files the extractor rejects (syntax error, non-UTF-8).

TWO TELEMETRY LAYERS, because they answer different questions:

* DYNAMIC — the refusal message the interpreter actually produced,
  bucketed and ranked. This is "what stops real programs FIRST".
* STATIC — every ``Unsupported`` node in the envelope, ranked by the
  Python AST kind (``py_kind``) the extractor recorded. This is the
  feature ladder's priority queue: what a file contains, not merely what
  it reached. NOTE an ``Unsupported`` node is a LEAF — its subtree is not
  extracted — so the in-tier node fraction is an UPPER BOUND on coverage,
  and is reported as such.

The model side runs as ONE ``leanmodels-run --script-batch`` process for
the whole corpus (one startup, not one per file); rows stream out as they
are produced, so a stalled file is identified by name rather than
swallowed.

Python 3.9 compatible.
"""

import argparse
import glob
import importlib.machinery
import importlib.util
import json
import os
import re
import subprocess
import sys
import threading
import time

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# tools/leanpy is the extension-less binary; load it as a module so the
# survey and the one-file runner share ONE extraction/runner path.
_path = os.path.join(REPO_ROOT, "tools", "leanpy")
_spec = importlib.util.spec_from_loader(
    "leanpy", importlib.machinery.SourceFileLoader("leanpy", _path))
leanpy = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(leanpy)
envelope_for = leanpy.envelope_for
runner_command = leanpy.runner_command
default_cache = leanpy.default_cache

MAGIC = re.compile(r"[*?\[]")


# ---------------------------------------------------------------------------
# corpus
# ---------------------------------------------------------------------------

def expand(patterns):
    out = []
    for pat in patterns:
        if os.path.isdir(pat):
            pat = os.path.join(pat, "*.py")
        hits = sorted(glob.glob(pat, recursive=True)) if MAGIC.search(pat) else [pat]
        for h in hits:
            if h.endswith(".py") and os.path.isfile(h) and h not in out:
                out.append(h)
    return out


def load_corpus(path, extra_paths):
    """[(group, [files...])] from a corpus file and/or command-line paths."""
    groups = []
    if path is not None:
        with open(path, "r", encoding="utf-8") as f:
            spec = json.load(f)
        for entry in spec:
            files = expand(entry["paths"])
            skip = set(entry.get("skip", []))
            files = [f for f in files if f not in skip]
            groups.append((entry["name"], files))
    if extra_paths:
        groups.append(("argv", expand(extra_paths)))
    return groups


# ---------------------------------------------------------------------------
# static census
# ---------------------------------------------------------------------------

# The exact-text import whitelist the model treats as benign
# (`benignImportBinds`, Ast.lean). Keep in sync — a whitelisted import is
# not a wall.
BENIGN_IMPORTS = frozenset((
    "import time",
    "from itertools import count",
    "from collections import namedtuple",
))


def census(envelope_path):
    """(total nodes, [py_kind ...], [wall ...]) of one envelope.

    The wall list is SORTED, not a set: it goes into the row that ``--json``
    writes, and a set makes ``json.dump`` raise — which it did, on every
    corpus, from the moment the wall census landed. An instrument whose
    machine-readable output cannot be produced is not an instrument.

    Every dict carrying a ``kind`` is a node; ``Unsupported`` ones
    contribute their ``py_kind``. The WALL SET is the third result and it
    is what makes the ranking honest: `runScript`'s admissions are
    ORDERED, so the dynamic telemetry only ever names the FIRST thing that
    stopped a file, and a wall that always sits behind another one looks
    like the frontier when it is not. Measured 2026-08-13: 112 stdlib
    files refuse on class creation and 111 of them also contain an import,
    so the class tier — however worthwhile as a language surface — would
    move the sweep by ONE file. A count that cannot say that is not
    telling you where to work.
    """
    with open(envelope_path, "r", encoding="utf-8") as f:
        env = json.load(f)
    total = 0
    kinds = []
    walls = set()
    stack = [env["module"]]
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
                        if node.get("text", "") not in BENIGN_IMPORTS:
                            walls.add("import")
                    else:
                        walls.add("node:" + py)
                elif k == "ClassDef" and node.get("creation_effects"):
                    walls.add("class-creation")
            stack.extend(node.values())
        elif isinstance(node, list):
            stack.extend(node)
    return total, kinds, sorted(walls)


# ---------------------------------------------------------------------------
# the model side: ONE batch process
# ---------------------------------------------------------------------------

def run_batch(runner, jobs, fuel, timeout):
    """Stream ``--script-batch`` results. Returns {envelope path: row}; a
    file that never produced a row is left out and reported as HUNG."""
    jobs_path = os.path.join(default_cache(), "survey-jobs.jsonl")
    with open(jobs_path, "w", encoding="utf-8") as f:
        for envelope in jobs:
            f.write(json.dumps({"path": envelope}) + "\n")
    cmd = list(runner) + ["--script-batch", jobs_path]
    if fuel is not None:
        cmd += ["--fuel", str(fuel)]
    proc = subprocess.Popen(cmd, cwd=REPO_ROOT, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, text=True)
    killed = []

    def watchdog():
        if proc.poll() is None:
            killed.append(True)
            proc.kill()
    timer = threading.Timer(timeout, watchdog)
    timer.start()
    rows = {}
    try:
        for line in proc.stdout:
            line = line.strip()
            if not line:
                continue
            row = json.loads(line)
            if "path" in row:
                rows[row["path"]] = row
            else:  # runner-error without a path: attribute to the next job
                rows.setdefault("__runner_error__", []).append(row)
    finally:
        timer.cancel()
        proc.wait()
    return rows, bool(killed)


def run_cpython(cpython, path, timeout):
    """The oracle: the file as a program. stdin is /dev/null — a corpus file
    that reads stdin must fail like a piped-from-nothing program, never hang
    the survey waiting for a keystroke."""
    try:
        with open(os.devnull, "rb") as devnull:
            proc = subprocess.run([cpython, os.path.abspath(path)], cwd=REPO_ROOT,
                                  stdin=devnull, capture_output=True, text=True,
                                  timeout=timeout)
        return proc.stdout, proc.returncode, proc.stderr, None
    except subprocess.TimeoutExpired:
        return None, None, None, "oracle timeout after %gs" % timeout
    except (OSError, UnicodeDecodeError) as e:
        return None, None, None, "oracle failed: %s" % e


TRACEBACK_CLASS = re.compile(r"^(?:[A-Za-z_][\w.]*\.)?([A-Za-z_]\w*)(?::.*)?$")


def cpython_exc_line(stderr):
    """The last traceback line, `ClassName: message` or a bare class."""
    for line in reversed((stderr or "").splitlines()):
        line = line.strip()
        if line:
            return line
    return None


def message_verdict(row, oracle_line):
    """How close the model's exception TEXT is to CPython's, given the
    classes already agree. Three honest buckets:

      SAME     the model carries a message and it matches CPython's line;
      DRIFT    it carries one and the text differs — a real (small) gap;
      ABSENT   the model's constructor carries no message at all, so there
               is nothing to compare and inventing one would be a claim
               the semantics does not make.
    """
    cls = row.get("exn")
    if "exnmsg" not in row:
        return ("ABSENT", cls, oracle_line)
    msg = row["exnmsg"]
    ours = cls if msg == "" else "%s: %s" % (cls, msg)
    return ("SAME" if ours == oracle_line else "DRIFT", ours, oracle_line)


def cpython_exc_class(stderr):
    """The exception CLASS of an oracle run that died, read off the last
    traceback line (`ModuleNotFoundError: No module named 'x'` -> the name;
    a class defined in the script prints qualified, `__main__.Stop`, and the
    last dotted component is the name the model reports).

    Without this the comparison is stdout + exit code only, and CPython maps
    EVERY uncaught exception to exit 1 — so two different exceptions look
    identical. `None` = unreadable, which the caller must report, never pass.
    """
    for line in reversed((stderr or "").splitlines()):
        line = line.strip()
        if not line:
            continue
        m = TRACEBACK_CLASS.match(line)
        return m.group(1) if m else None
    return None


def default_oracle():
    """The PINNED reference interpreter when it is installed. The model's
    tier is specified against CPython 3.9 (docs/backlog.md), so surveying
    against a newer python3 would report version drift as model divergence."""
    for cand in ("python3.9", "python3"):
        try:
            if subprocess.run([cand, "-c", ""], capture_output=True).returncode == 0:
                return cand
        except OSError:
            continue
    return sys.executable


def lean_stdout(row):
    return "".join(line + "\n" for line in row.get("stdout", []))


# ---------------------------------------------------------------------------

def main(argv=None):
    parser = argparse.ArgumentParser(prog="leanpy_survey.py")
    parser.add_argument("paths", nargs="*", metavar="PATH_OR_GLOB")
    parser.add_argument("--corpus", default=None)
    parser.add_argument("--stdlib", action="store_true",
                        help="add the WILD SWEEP group: the pinned oracle's "
                        "top-level stdlib modules minus the safety list "
                        "(harness/import_closure.py SAFETY). Deliberately NOT "
                        "in the default corpus — running arbitrary stdlib top "
                        "level under the oracle has side effects — but pinned "
                        "in code so the measurement is reproducible.")
    parser.add_argument("--fuel", type=int, default=200000)
    parser.add_argument("--no-cpython", action="store_true")
    parser.add_argument("--cpython", default=os.environ.get("LEANPY_CPYTHON") or default_oracle())
    parser.add_argument("--cpython-timeout", type=float, default=20.0)
    parser.add_argument("--batch-timeout", type=float, default=900.0)
    parser.add_argument("--limit", type=int, default=None,
                        help="at most N files per group (a quick sweep)")
    parser.add_argument("--exclude", default=None, metavar="REGEX",
                        help="drop files whose path matches (a wild sweep's "
                        "safety list: stdlib modules whose top level opens a "
                        "browser or a window)")
    parser.add_argument("--json", dest="json_out", default=None)
    parser.add_argument("--top", type=int, default=12, help="histogram rows to print")
    opts = parser.parse_args(argv)

    os.chdir(REPO_ROOT)
    if not opts.corpus:
        opts.corpus = None
    if opts.corpus is None and not opts.paths and not opts.stdlib:
        opts.corpus = os.path.join("harness", "leanpy_corpus.json")
    groups = load_corpus(opts.corpus, opts.paths)
    if opts.stdlib:
        import import_closure
        table = import_closure.ModuleTable.of(opts.cpython)
        groups.append(("cpython-%s-stdlib" % table.version,
                       import_closure.stdlib_seeds(table)))
    if opts.exclude:
        drop = re.compile(opts.exclude)
        groups = [(n, [f for f in fs if not drop.search(f)]) for n, fs in groups]
    if opts.limit is not None:
        groups = [(n, fs[:opts.limit]) for n, fs in groups]

    cache = default_cache()
    os.makedirs(cache, exist_ok=True)
    runner = runner_command(build=False)

    oracle_version = "(not run)"
    if not opts.no_cpython:
        v = subprocess.run([opts.cpython, "-VV"], capture_output=True, text=True)
        oracle_version = (v.stdout or v.stderr).strip().splitlines()[0]

    # 1. extract everything (loud per-file failures are their own category)
    results = []          # dicts, one per file
    jobs = []             # envelope paths, batch order
    by_envelope = {}
    for group, files in groups:
        for src in files:
            rec = {"group": group, "file": src}
            envelope = envelope_for(src, cache)
            if envelope is None:
                rec["verdict"] = "EXTRACT"
                rec["detail"] = "extractor refused (see stderr above)"
            else:
                rec["envelope"] = envelope
                total, kinds, walls = census(envelope)
                rec["nodes"] = total
                rec["unsupported_kinds"] = kinds
                rec["walls"] = walls
                jobs.append(envelope)
                by_envelope[envelope] = rec
            results.append(rec)

    # 2. ONE batch process for the whole corpus
    t0 = time.time()
    rows, killed = run_batch(runner, jobs, opts.fuel, opts.batch_timeout)
    batch_secs = time.time() - t0

    # 3. the oracle, then the verdicts
    for rec in results:
        if rec.get("verdict") == "EXTRACT":
            continue
        row = rows.get(rec["envelope"])
        if row is None:
            rec["verdict"] = "HUNG"
            rec["detail"] = ("no row from the batch (killed after %gs)" % opts.batch_timeout
                             if killed else "no row from the batch")
            continue
        rec["status"] = row["status"]
        rec["exit"] = row.get("exit")
        rec["msg"] = row.get("msg")
        rec["live"] = row.get("live")
        if row["status"] == "unsupported":
            rec["verdict"] = "REFUSE"
            rec["detail"] = row["msg"]
            continue
        if row["status"] == "timeout":
            rec["verdict"] = "TIMEOUT"
            rec["detail"] = "fuel %d exhausted" % opts.fuel
            continue
        if row["status"] == "runner-error":
            rec["verdict"] = "RUNNER"
            rec["detail"] = row.get("msg", "")
            continue
        if opts.no_cpython:
            rec["verdict"] = "RAN"
            rec["detail"] = "exit %d, %d stdout lines (no oracle)" % (
                row["exit"], len(row.get("stdout", [])))
            continue
        out, code, cerr, err = run_cpython(opts.cpython, rec["file"], opts.cpython_timeout)
        if err is not None:
            rec["verdict"] = "ORACLE"
            rec["detail"] = err
            continue
        # An `exn` outcome must agree on the exception CLASS as well: CPython
        # exits 1 for every uncaught exception, so stdout + exit code alone
        # cannot tell a ZeroDivisionError from a NameError.
        if row["status"] == "exn":
            oracle_exc = cpython_exc_class(cerr)
            if oracle_exc != row.get("exn"):
                rec["verdict"] = "DIVERGE"
                rec["detail"] = ("lean raised %s | cpython raised %s"
                                 % (row.get("exn"),
                                    oracle_exc if oracle_exc else
                                    "an exception whose class could not be read"))
                continue
            # One resolution step below the class: the MESSAGE. Reported,
            # not enforced — the model's payload-free constructors carry no
            # message at all (`IndexError` is three different CPython texts),
            # and a bucket that says which is the useful instrument. The
            # class comparison above is what fails a run.
            rec["msg_verdict"] = message_verdict(row, cpython_exc_line(cerr))
        if out == lean_stdout(row) and code == row["exit"]:
            rec["verdict"] = "MATCH"
            rec["stdout_bytes"] = len(out)
            rec["detail"] = "exit %d, %d stdout bytes, %s live stmts" % (
                code, len(out), row.get("live"))
        else:
            rec["verdict"] = "DIVERGE"
            rec["detail"] = ("lean exit %d stdout %r | cpython exit %d stdout %r"
                             % (row["exit"], lean_stdout(row), code, out))

    # 4. the report
    order = ["MATCH", "DIVERGE", "REFUSE", "TIMEOUT", "ORACLE", "EXTRACT", "HUNG",
             "RUNNER", "RAN"]
    counts = {k: 0 for k in order}
    for rec in results:
        counts[rec["verdict"]] = counts.get(rec["verdict"], 0) + 1

    for group, _ in groups:
        print("=" * 78)
        print("group %s" % group)
        for rec in results:
            if rec["group"] != group:
                continue
            print("  %-8s %-46s %s" % (rec["verdict"], rec["file"],
                                       (rec.get("detail") or "")[:110]))

    comparable = counts["MATCH"] + counts["DIVERGE"] + counts["REFUSE"] + counts["TIMEOUT"]
    print("=" * 78)
    print("oracle: %s" % oracle_version)
    print("%d files in %d groups; model side: one batch process, %.1fs"
          % (len(results), len(groups), batch_secs))
    print("  " + "  ".join("%s=%d" % (k, counts[k]) for k in order if counts[k]))
    speaking = sum(1 for r in results if r.get("stdout_bytes"))
    stepping = sum(1 for r in results if r["verdict"] == "MATCH" and r.get("live"))
    if comparable:
        print("  COMPLETENESS: %d/%d = %.1f%% of oracle-comparable files run under the "
              "model and match CPython" % (counts["MATCH"], comparable,
                                           100.0 * counts["MATCH"] / comparable))
        print("    of those %d matches: %d executed live top-level statements, %d printed "
              "something; the remaining %d are definitions-only modules (live=0 — ingested "
              "and module-initialized, agreeing on an empty stdout)"
              % (counts["MATCH"], stepping, speaking, counts["MATCH"] - stepping))
    print("  DIVERGENCES: %d (any nonzero is a bug in the model)" % counts["DIVERGE"])

    # exception-MESSAGE telemetry (2026-08-13): the classes already agree
    # wherever a run raised, so this is the next resolution step down —
    # reported, never a verdict (see `message_verdict`).
    mv = [rec["msg_verdict"] for rec in results if rec.get("msg_verdict")]
    if mv:
        print("-" * 78)
        buckets = {}
        for kind, _, _ in mv:
            buckets[kind] = buckets.get(kind, 0) + 1
        print("EXCEPTION-MESSAGE telemetry (classes already agree; text is the next step down):")
        print("    " + "  ".join("%s=%d" % (k, buckets[k]) for k in sorted(buckets)))
        for kind, ours, theirs in mv:
            if kind != "SAME":
                print("    %-6s model %-40s cpython %s"
                      % (kind, (ours or "-")[:40], (theirs or "-")[:60]))

    # dynamic telemetry
    dyn = {}
    for rec in results:
        if rec["verdict"] == "REFUSE":
            dyn[rec["detail"]] = dyn.get(rec["detail"], 0) + 1
    if dyn:
        print("-" * 78)
        print("DYNAMIC telemetry — what actually stopped the run, ranked:")
        for msg, n in sorted(dyn.items(), key=lambda kv: -kv[1])[:opts.top]:
            print("  %4d  %s" % (n, msg[:100]))

    # SOLE-BLOCKER telemetry (2026-08-13): what removing one wall would
    # ACTUALLY buy. `present` counts refusing files containing the wall at
    # all — the number the ordered dynamic ranking flatters — and `sole`
    # counts those where it is the ONLY wall, which is the number of files
    # a tier closing it would move.
    refusing = [rec for rec in results
                if rec["verdict"] == "REFUSE" and "walls" in rec]
    if refusing:
        present, sole = {}, {}
        for rec in refusing:
            ws = rec["walls"] or ["(none detected statically)"]
            for w in ws:
                present[w] = present.get(w, 0) + 1
            if len(ws) == 1:
                w = next(iter(ws))
                sole[w] = sole.get(w, 0) + 1
        print("-" * 78)
        print("SOLE-BLOCKER telemetry — %d refusing files; `sole` is what a tier "
              "would actually buy:" % len(refusing))
        order = sorted(present, key=lambda w: (-sole.get(w, 0), -present[w]))
        for w in order[:opts.top]:
            print("  sole %4d   present %4d   %s" % (sole.get(w, 0), present[w], w))

    # static telemetry
    stat = {}
    files_with = {}
    nodes = 0
    unsupported = 0
    for rec in results:
        if "unsupported_kinds" not in rec:
            continue
        nodes += rec["nodes"]
        unsupported += len(rec["unsupported_kinds"])
        for k in rec["unsupported_kinds"]:
            stat[k] = stat.get(k, 0) + 1
        for k in set(rec["unsupported_kinds"]):
            files_with[k] = files_with.get(k, 0) + 1
    if nodes:
        print("-" * 78)
        print("STATIC telemetry — Unsupported nodes by Python AST kind "
              "(the ladder's priority queue):")
        print("  in-tier nodes: %d/%d = %.1f%% (UPPER BOUND: an Unsupported node "
              "hides its subtree)" % (nodes - unsupported, nodes,
                                      100.0 * (nodes - unsupported) / nodes))
        for k, n in sorted(stat.items(), key=lambda kv: -kv[1])[:opts.top]:
            print("  %6d nodes  in %3d files   %s" % (n, files_with[k], k))

    if opts.json_out:
        with open(opts.json_out, "w", encoding="utf-8") as f:
            json.dump({"oracle": oracle_version, "fuel": opts.fuel,
                       "batch_seconds": batch_secs, "counts": counts,
                       "static": stat, "dynamic": dyn, "files": results}, f, indent=2)
            f.write("\n")
        print("wrote %s" % opts.json_out)

    bad = counts["DIVERGE"] + counts["HUNG"] + counts["RUNNER"]
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
