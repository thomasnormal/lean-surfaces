#!/usr/bin/env python3
"""library_survey.py — LIBRARY MODE: verify a module you can only IMPORT.

    python3 harness/library_survey.py [--corpus harness/library_corpus.json]
                                      [--only REGEX] [--limit N] [--max-calls N]
                                      [--json OUT] [--build-manifest] [--determinism]

THE METRIC, in the owner's words (2026-08-15): library mode is "import
this module, then verify its public functions behave identically to
CPython's" — "we should be able to verify modules that we just import,
but don't have a way to run."

Program mode (`harness/leanpy_survey.py`) runs a FILE and compares stdout
and exit code. Most of the Python that matters is not a program: a
library's meaning is in what its functions RETURN, and a corpus of
libraries surveyed in program mode reports a wall of vacuous agreements
(empty stdout equals empty stdout) that says nothing about the module.
This survey answers the other question, in two phases:

  BODY   the module's top level runs under CPython (as an IMPORT — a fresh
         module object whose `__name__` is the module name) and under the
         model (`leanmodels-run --script-batch`). stdout, the exception
         CLASS and — where the model carries one — the exception MESSAGE
         must agree.
  CALLS  for a module whose body agreed, every public function the FILE
         defines is driven on a deterministic battery (its own doctests,
         plus type-driven generated inputs) through the typed-call runner
         (`leanmodels-run --batch`), and each return value / exception is
         compared against CPython's.

VERDICTS, per module:

  VERIFIED   body agreed and every driven call agreed (with the call count —
             a verdict without its denominator is a slogan)
  BODY-ONLY  body agreed and the battery is empty (no drivable public
             function): reported apart from VERIFIED, never folded into it
  PARTIAL    body agreed, N of M calls agreed — the rest are listed
  REFUSED    the model refused loudly, and the named construct IS the datum
  DIVERGED   a silent mismatch anywhere. The headline. Any DIVERGED row
             fails the run (exit 1).
  ORACLE     CPython itself could not import the module — excluded, reported

THE IMPORT-SEMANTICS GATE. The model has no import machinery: Script.lean's
`scriptNameBinding` binds `__name__ = "__main__"`, which is PROGRAM
semantics. For a module that never reads `__name__` at import time the two
coincide and the model's body run is a library-mode answer. For a module
that does, it is not — so this survey REFUSES such a module with the named
construct `import-semantics:__name__` instead of comparing a program-mode
run against an import-mode oracle and calling the difference a divergence.
The gate fires only where the model would otherwise have claimed a body
match, so it can never hide a refusal the model itself produced.

BOTH ENDS ARE PINNED, separately, exactly as in program mode: the FRONTEND
by re-exec into CPython 3.9 (`_reexec_under_pinned_frontend`, the pattern
`harness/leanpy_survey.py` and `harness/diff_test.py` established), and the
ORACLE by `--cpython` / `LEANPY_CPYTHON`.

DETERMINISM is a property this instrument must be able to demonstrate, not
claim: `--determinism` runs the whole survey twice and compares the battery
BYTES. Nothing in the battery reads the wall clock, `hash()`, or set
iteration order.

Python 3.9 compatible.
"""

import argparse
import ast
import glob
import importlib.machinery
import importlib.util
import json
import os
import re
import subprocess
import sys
import tempfile
import threading
import time

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def _reexec_under_pinned_frontend():
    """RUN THE FRONTEND ON THE PINNED INTERPRETER — the pattern of
    `harness/leanpy_survey.py` (2026-08-15) and `harness/diff_test.py`
    (2026-08-13), copied rather than imported because importing that module
    is what triggers ITS re-exec, which would replace this process with
    that script.

    The envelope is built by running the extractor under `sys.executable`
    (tools/leanpy `envelope_for`), so an unpinned frontend shows the model
    a different program than the oracle runs. If the pin is not installed,
    say so LOUDLY and keep going, never quietly."""
    if os.environ.get("LEANPY_NO_REEXEC"):
        return
    want = os.environ.get("LEANPY_FRONTEND") or "python3.9"
    if sys.version_info[:2] == (3, 9) and not os.environ.get("LEANPY_FRONTEND"):
        return
    from shutil import which
    exe = which(want)
    if exe is None:
        print("harness/library_survey.py: WARNING the pinned frontend %r is not "
              "installed; extracting with %s instead — the model may be shown a "
              "different program than the oracle imports"
              % (want, sys.version.split()[0]), file=sys.stderr)
        return
    if os.path.realpath(exe) == os.path.realpath(sys.executable):
        return
    os.environ["LEANPY_NO_REEXEC"] = "1"
    os.execv(exe, [exe, os.path.abspath(__file__)] + sys.argv[1:])


_reexec_under_pinned_frontend()
# Set unconditionally: the imports below reach modules that re-exec on
# import, and this process has already made the pin decision above.
os.environ["LEANPY_NO_REEXEC"] = "1"

_path = os.path.join(REPO_ROOT, "tools", "leanpy")
_spec = importlib.util.spec_from_loader(
    "leanpy", importlib.machinery.SourceFileLoader("leanpy", _path))
leanpy = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(leanpy)
sys.path.insert(0, os.path.join(REPO_ROOT, "harness"))
import leanpy_survey                     # noqa: E402  (census + oracle helpers, ONE definition)
import import_closure                    # noqa: E402  (the module table, SAFETY)

CENSUS_JSON = os.path.join(REPO_ROOT, "docs", "class-tier-census.json")
CEILING_JSON = os.path.join(REPO_ROOT, "docs", "import-ceiling-census.json")
MANIFEST = os.path.join(REPO_ROOT, "harness", "library_corpus.json")
ORACLE = os.path.join(REPO_ROOT, "harness", "library_oracle.py")


# ---------------------------------------------------------------------------
# the corpus manifest
# ---------------------------------------------------------------------------

IN_REPO_GROUPS = (
    ("examples", "Examples/python/*/*.py"),
    ("repo-scripts", "harness/scripts/*.py"),
    ("cpython-lib-test", "vendor/cpython-3.9-lib-test/*.py"),
)


def _module_ast(path):
    with open(path, "rb") as f:
        return ast.parse(f.read(), filename=path)


def import_time_nodes(tree):
    """Every AST node that EXECUTES at import time.

    Function and lambda BODIES are excluded (they run when called, not when
    imported); a class body is included, because CPython executes it at the
    `class` statement. Decorator lists and default expressions ARE included
    for the same reason — they are evaluated at the `def`."""
    out = []
    stack = list(tree.body)
    while stack:
        node = stack.pop()
        out.append(node)
        for name, child in ast.iter_fields(node):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)) \
                    and name == "body":
                continue
            if isinstance(child, list):
                stack.extend(c for c in child if isinstance(c, ast.AST))
            elif isinstance(child, ast.AST):
                stack.append(child)
    return out


def reads_name_dunder(tree):
    """Does the module read `__name__` at IMPORT time? (line or None)

    The import-semantics gate. The model binds `"__main__"`; an import binds
    the module's name. A module that never looks cannot tell the two apart,
    and that is the whole condition under which a program-mode body run is
    also a library-mode answer."""
    for node in import_time_nodes(tree):
        if isinstance(node, ast.Name) and node.id == "__name__":
            return getattr(node, "lineno", 0)
    return None


def library_shaped(path):
    """Is this in-repo file one program mode CANNOT exercise?

    The owner's set: "modules that we just import, but don't have a way to
    run". Statically: it defines at least one public function, and running
    it as a program does nothing observable — no top-level `print`, and no
    `if __name__ == "__main__":` block to run under one. Such a file's
    program-mode MATCH is empty stdout against empty stdout, which is a
    verdict about nothing."""
    try:
        tree = _module_ast(path)
    except (SyntaxError, UnicodeDecodeError, OSError):
        return False, "unparsable"
    publics = [s.name for s in tree.body
               if isinstance(s, ast.FunctionDef) and not s.name.startswith("_")]
    if not publics:
        return False, "no public function"
    for node in import_time_nodes(tree):
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) \
                and node.func.id == "print":
            return False, "prints at import time"
    if reads_name_dunder(tree) is not None:
        return False, "has a __main__ guard (program mode runs it)"
    return True, "%d public function(s), no observable program behaviour" % len(publics)


def expected_wall(walls, class_walled):
    """The census's PREDICTION for this module, in the four-way vocabulary
    the backlog uses: none / class / import / node:<construct>.

    Ordered the way `runScript` admits: `classesCreationPure` is its FIRST
    check (docs/backlog.md §THE CLASS-CREATION WALL — "the 106 is a cliff of
    ADMISSION ORDER"), so a class-walled module is predicted to stop there
    whatever else it contains."""
    if class_walled:
        return "class-creation"
    if "import" in walls:
        return "import"
    others = [w for w in walls if w != "import"]
    if others:
        return sorted(others)[0]
    return "none"


def build_manifest(out_path):
    """Write the corpus manifest: the census's 141 pure-Python library
    modules, plus the in-repo files program mode cannot exercise.

    Every row carries its PROVENANCE and the census's own prediction, so the
    scoreboard can be reconciled against the censuses row by row and any
    module whose observed wall differs from the predicted one is a finding
    rather than a footnote."""
    with open(CENSUS_JSON, "r", encoding="utf-8") as f:
        census = json.load(f)
    ceiling = {}
    if os.path.exists(CEILING_JSON):
        with open(CEILING_JSON, "r", encoding="utf-8") as f:
            for row in json.load(f)["rows"]:
                ceiling[row["module"]] = row
    rows = []
    for rec in census["library"]:
        seed = ceiling.get(rec["module"])
        rows.append({
            "module": rec["module"],
            "file": rec["file"],
            "provenance": "census:library",
            "source": "docs/class-tier-census.json (CPython %s)" % census["cpython"],
            "census_walls": rec["walls"],
            "census_class_walled": rec["class_walled"],
            "census_classes": rec["nclasses"],
            "expected_wall": expected_wall(rec["walls"], rec["class_walled"]),
            "c_reaching": (None if seed is None else bool(seed["full_c"])),
        })
    for group, pattern in IN_REPO_GROUPS:
        for path in sorted(glob.glob(os.path.join(REPO_ROOT, pattern))):
            rel = os.path.relpath(path, REPO_ROOT)
            ok, why = library_shaped(path)
            if not ok:
                continue
            envelope = leanpy.envelope_for(rel, leanpy.default_cache())
            walls = [] if envelope is None else leanpy_survey.census(envelope)[2]
            class_walled = "class-creation" in walls
            rows.append({
                "module": os.path.splitext(os.path.basename(path))[0],
                "file": rel,
                "provenance": "in-repo:" + group,
                "source": why,
                "census_walls": walls,
                "census_class_walled": class_walled,
                "census_classes": None,
                "expected_wall": expected_wall(walls, class_walled),
                "c_reaching": False,
            })
    manifest = {
        "metric": ("library mode: import this module, then verify its public "
                   "functions behave identically to CPython's (owner, 2026-08-15)"),
        "cpython": census["cpython"],
        "generated_by": "harness/library_survey.py --build-manifest",
        "modules": rows,
    }
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(manifest, f, indent=1, sort_keys=True)
        f.write("\n")
    return manifest


# ---------------------------------------------------------------------------
# the model side
# ---------------------------------------------------------------------------

def run_script_batch(runner, envelopes, fuel, timeout):
    """The BODY phase: every module's top level in ONE runner process
    (`--script-batch`). Returns ({envelope: row}, killed).

    THE JOBS FILE IS KEYED BY PID. The corpus is surveyed in disjoint chunks
    when one process cannot own the machine long enough to finish it, and
    those chunks run CONCURRENTLY — with a fixed filename in the shared
    envelope cache, one chunk overwrites the jobs another chunk's runner is
    about to read. The call phase pairs results to jobs POSITIONALLY, so a
    same-length cross would mispair silently: a verdict attached to the wrong
    call, which is the one failure this survey must never produce."""
    jobs_path = os.path.join(leanpy.default_cache(), "library-body-jobs-%d.jsonl" % os.getpid())
    with open(jobs_path, "w", encoding="utf-8") as f:
        for envelope in envelopes:
            f.write(json.dumps({"path": envelope}) + "\n")
    cmd = list(runner) + ["--script-batch", jobs_path, "--fuel", str(fuel)]
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
            if line.startswith("{"):
                row = json.loads(line)
                if "path" in row:
                    rows[row["path"]] = row
    finally:
        timer.cancel()
        proc.wait()
    return rows, bool(killed)


def run_call_batch(runner, jobs, fuel, timeout):
    """The CALLS phase: every battery call in ONE runner process
    (`--batch`). Returns a list positionally paired with `jobs`; a runner
    that dies early yields explicit `runner-error` rows for the tail, never
    a silently shortened table (harness/diff_test.py's rule)."""
    jobs_path = os.path.join(leanpy.default_cache(), "library-call-jobs-%d.jsonl" % os.getpid())
    with open(jobs_path, "w", encoding="utf-8") as f:
        for job in jobs:
            f.write(json.dumps(job, separators=(",", ":")) + "\n")
    cmd = list(runner) + ["--batch", jobs_path, "--fuel", str(fuel)]
    proc = subprocess.Popen(cmd, cwd=REPO_ROOT, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, text=True)
    killed = []

    def watchdog():
        if proc.poll() is None:
            killed.append(True)
            proc.kill()
    timer = threading.Timer(timeout, watchdog)
    timer.start()
    out = []
    try:
        for line in proc.stdout:
            line = line.strip()
            if not line.startswith("{"):
                continue
            if len(out) >= len(jobs):
                raise RuntimeError("the runner printed more results than the %d jobs — "
                                   "the pairing is broken, refusing to guess" % len(jobs))
            out.append(json.loads(line))
    finally:
        timer.cancel()
        proc.wait()
    while len(out) < len(jobs):
        out.append({"status": "runner-error",
                    "msg": "runner exited (code %s) after %d/%d results%s"
                           % (proc.returncode, len(out), len(jobs),
                              " (killed by the watchdog)" if killed else "")})
    return out


# ---------------------------------------------------------------------------
# the oracle side
# ---------------------------------------------------------------------------

def run_oracle(cpython, module, path, calls, max_calls, timeout, scratch):
    """One `harness/library_oracle.py` subprocess: import the module under
    IMPORT semantics and (optionally) drive its public functions.

    A SUBPROCESS and not an in-process import, unlike diff_test.py: this
    corpus is the real stdlib, its bodies run at import, and one module that
    hangs or exits must cost one row and not the survey. `cwd` is a scratch
    directory so a function that writes a file writes it there, and
    PYTHONHASHSEED is pinned so nothing the oracle observes depends on the
    salt."""
    out_path = os.path.join(scratch, "oracle.json")
    cmd = [cpython, ORACLE, "--module", module, "--file", path, "--out", out_path,
           "--max-calls", str(max_calls)]
    if calls:
        cmd.append("--calls")
    env = dict(os.environ, PYTHONHASHSEED="0", PYTHONDONTWRITEBYTECODE="1")
    try:
        proc = subprocess.run(cmd, cwd=scratch, capture_output=True, text=True,
                              timeout=timeout, env=env)
    except subprocess.TimeoutExpired:
        return {"status": "oracle-error", "msg": "oracle timeout after %gs" % timeout}
    if not os.path.exists(out_path):
        return {"status": "oracle-error",
                "msg": "oracle produced no result (exit %d): %s"
                       % (proc.returncode, (proc.stderr or "").strip()[-400:])}
    with open(out_path, "r", encoding="utf-8") as f:
        result = json.load(f)
    os.unlink(out_path)
    return result


# ---------------------------------------------------------------------------
# comparison
# ---------------------------------------------------------------------------

def _by_module(index):
    """[(row, how many consecutive jobs it owns)] over the job index, which is
    built module by module, so a module's jobs are contiguous by construction."""
    out = []
    for row, _fname, _i in index:
        if out and out[-1][0] is row:
            out[-1][1] += 1
        else:
            out.append([row, 1])
    return [(row, n) for row, n in out]


def lean_stdout(row):
    return "".join(line + "\n" for line in row.get("stdout", []))


def compare_body(model, oracle):
    """(verdict, detail) for the BODY phase — `MATCH`, `DIVERGE`, `ORACLE`.

    stdout must agree; an exception must agree on CLASS; and where the model
    CARRIES a message it must agree on the message too (the message tier of
    `harness/leanpy_survey.py`: SAME / DRIFT / ABSENT — a model constructor
    that carries no message makes no claim, and inventing one for it would
    be a claim the semantics does not make)."""
    ostatus = oracle.get("status")
    if ostatus == "oracle-error":
        return "ORACLE", oracle.get("msg", "")
    mout, oout = lean_stdout(model), oracle.get("stdout", "")
    if model["status"] == "ok" and ostatus == "ok":
        if mout != oout:
            return "DIVERGE", "stdout %r vs cpython %r" % (mout[:200], oout[:200])
        return "MATCH", "body ran, %d stdout byte(s)" % len(oout)
    if model["status"] == "exn" and ostatus == "exn":
        if model.get("exn") != oracle.get("exn"):
            return "DIVERGE", ("lean raised %s | cpython raised %s"
                               % (model.get("exn"), oracle.get("exn")))
        if mout != oout:
            return "DIVERGE", "same exception, stdout %r vs %r" % (mout[:200], oout[:200])
        if "exnmsg" not in model:
            return "MATCH", "raised %s (message tier ABSENT)" % model.get("exn")
        if model["exnmsg"] != oracle.get("exnmsg", ""):
            return "DIVERGE", ("%s message %r vs cpython %r"
                               % (model.get("exn"), model["exnmsg"], oracle.get("exnmsg")))
        return "MATCH", "raised %s: %s" % (model.get("exn"), model["exnmsg"])
    return "DIVERGE", ("lean %s | cpython %s%s"
                       % (model["status"], ostatus,
                          " (%s)" % oracle.get("exn") if ostatus == "exn" else ""))


def compare_call(model, oracle):
    """(verdict, detail) for ONE battery call.

    UNCOMPARABLE is a first-class answer and never agreement: the typed-call
    protocol (`leanmodels-run --batch`) carries a VALUE and an exception
    CLASS and nothing else, so a call whose CPython answer is outside the
    canonical value set, or that printed, or that mutated its arguments, is
    a call this protocol cannot adjudicate. Counting those as matches would
    be exactly the silent agreement this project exists not to produce."""
    mstatus, ostatus = model.get("status"), oracle.get("status")
    if mstatus == "unsupported":
        return "REFUSED", model.get("msg", "")
    if mstatus == "timeout":
        return "TIMEOUT", "fuel exhausted on this call"
    if mstatus == "runner-error":
        return "RUNNER", model.get("msg", "")
    if ostatus == "oracle-timeout":
        return "UNCOMPARABLE", "the oracle call timed out"
    if ostatus == "unmappable":
        return "UNCOMPARABLE", "cpython returned %s (outside the canonical value set)" % oracle.get("type")
    if oracle.get("stdout"):
        return "UNCOMPARABLE", "the call printed; --batch reports no stdout"
    if mstatus == "ok" and ostatus == "ok":
        if model.get("value") != oracle.get("value"):
            return "DIVERGE", "lean %s | cpython %s" % (json.dumps(model.get("value")),
                                                        json.dumps(oracle.get("value")))
        if oracle.get("mutated"):
            return "UNCOMPARABLE", "value agrees but the call MUTATED its arguments; " \
                                   "--batch reports no post-call heap"
        return "MATCH", ""
    if mstatus == "exn" and ostatus == "exn":
        if model.get("exn") != oracle.get("exn"):
            return "DIVERGE", "lean raised %s | cpython raised %s" % (model.get("exn"),
                                                                      oracle.get("exn"))
        return "MATCH", ""
    return "DIVERGE", "lean %s | cpython %s" % (json.dumps(model), json.dumps(oracle))


# ---------------------------------------------------------------------------

def survey(opts):
    with open(opts.corpus, "r", encoding="utf-8") as f:
        manifest = json.load(f)
    modules = manifest["modules"]
    if opts.only:
        pat = re.compile(opts.only)
        modules = [m for m in modules if pat.search(m["module"]) or pat.search(m["file"])]
    if opts.limit:
        modules = modules[:opts.limit]

    cache = leanpy.default_cache()
    os.makedirs(cache, exist_ok=True)
    runner = opts.runner.split() if opts.runner else leanpy.runner_command(build=False)
    # The stdlib sweep's safety list is a CORPUS invariant, not a suggestion:
    # those modules' bodies open a browser, a window or a socket, and library
    # mode IMPORTS bodies for a living.
    unsafe = [m["module"] for m in modules if m["module"] in import_closure.SAFETY]
    if unsafe:
        raise SystemExit("library_survey: the corpus contains %s, which harness/"
                         "import_closure.py SAFETY excludes from any sweep" % ", ".join(unsafe))
    rows = []
    envelopes = []
    for rec in modules:
        row = dict(rec)
        path = rec["file"] if os.path.isabs(rec["file"]) else os.path.join(REPO_ROOT, rec["file"])
        row["path"] = path
        if not os.path.exists(path):
            row["verdict"] = "MISSING"
            row["detail"] = "no such file"
            rows.append(row)
            continue
        envelope = leanpy.envelope_for(path, cache)
        if envelope is None:
            row["verdict"] = "EXTRACT"
            row["detail"] = "the extractor refused (see stderr)"
            rows.append(row)
            continue
        row["envelope"] = envelope
        envelopes.append(envelope)
        rows.append(row)

    t0 = time.time()
    body_rows, killed = run_script_batch(runner, envelopes, opts.fuel, opts.batch_timeout)
    body_secs = time.time() - t0

    # --- BODY verdicts -----------------------------------------------------
    scratch = tempfile.mkdtemp(prefix="libmode-")
    live = []
    for row in rows:
        if "envelope" not in row:
            continue
        model = body_rows.get(row["envelope"])
        if model is None:
            row["verdict"] = "HUNG"
            row["detail"] = ("no row from the batch%s"
                             % (" (killed after %gs)" % opts.batch_timeout if killed else ""))
            continue
        row["model_body"] = model["status"]
        if model["status"] == "unsupported":
            row["verdict"] = "REFUSED"
            row["detail"] = model.get("msg", "")
            row["observed_wall"] = wall_of(model.get("msg", ""))
            continue
        if model["status"] == "timeout":
            row["verdict"] = "TIMEOUT"
            row["observed_wall"] = "timeout"
            row["detail"] = "fuel %d exhausted on the module body" % opts.fuel
            continue
        if model["status"] == "runner-error":
            row["verdict"] = "RUNNER"
            row["detail"] = model.get("msg", "")
            continue
        # The model RAN the body. Before comparing, the import-semantics gate.
        try:
            gate = reads_name_dunder(_module_ast(row["path"]))
        except (SyntaxError, UnicodeDecodeError, OSError) as e:
            gate, row["gate_error"] = None, str(e)
        if gate is not None:
            row["verdict"] = "REFUSED"
            row["observed_wall"] = "import-semantics:__name__"
            row["detail"] = ("the model ran the body as a PROGRAM (`__name__` = '__main__', "
                             "Script.lean scriptNameBinding) but this module reads `__name__` "
                             "at import time (line %d) — no import mode exists to compare"
                             % gate)
            continue
        live.append(row)

    for row in live:
        oracle = run_oracle(opts.cpython, row["module"], row["path"], True,
                            opts.max_calls, opts.oracle_timeout, scratch)
        row["oracle"] = oracle
        model = body_rows[row["envelope"]]
        verdict, detail = compare_body(model, oracle.get("body", oracle))
        row["body_verdict"] = verdict
        if verdict != "MATCH":
            row["verdict"] = "DIVERGED" if verdict == "DIVERGE" else verdict
            row["detail"] = detail
        else:
            row["detail"] = detail

    # --- CALL phase --------------------------------------------------------
    jobs, index = [], []
    for row in live:
        if row.get("body_verdict") != "MATCH":
            continue
        for fn in row["oracle"].get("functions", []):
            for i, call in enumerate(fn.get("calls", [])):
                jobs.append({"path": row["envelope"], "function": fn["name"],
                             "args": call["args"], "fuel": opts.call_fuel})
                index.append((row, fn["name"], i))
    # ONE RUNNER PROCESS PER MODULE, each with its own wall-clock bound.
    #
    # FUEL IS A DEPTH BOUND, NOT A TIME BOUND — measured, and it cost two full
    # sweeps before it was understood: `fib(30)` at fuel 10000 returns 832040,
    # because ~2.7M calls at depth 30 never approach the limit. So `fib(100)`,
    # a perfectly ordinary row of the generated battery, runs effectively
    # forever and never times out. With one batch for the whole corpus that
    # single call ate the watchdog and took 239 later calls down with it. Per
    # module, it costs its own module a loud INCOMPLETE and nothing else.
    #
    # The batch shape is still load-bearing WITHIN a module (never one process
    # per row); a prebuilt binary starts in milliseconds, so per-module is the
    # cheapest granularity that isolates a runaway.
    t1 = time.time()
    call_results = []
    if jobs:
        start = 0
        for _, group in _by_module(index):
            end = start + group
            call_results.extend(run_call_batch(runner, jobs[start:end], opts.call_fuel,
                                               opts.module_timeout))
            start = end
    call_secs = time.time() - t1

    for (row, fname, i), model in zip(index, call_results):
        oracle = None
        for fn in row["oracle"]["functions"]:
            if fn["name"] == fname:
                oracle = fn["calls"][i]
        verdict, detail = compare_call(model, oracle["oracle"])
        row.setdefault("calls", []).append({
            "function": fname, "args": oracle["args"], "source": oracle["source"],
            "verdict": verdict, "detail": detail,
            "lean": model, "cpython": oracle["oracle"],
        })

    # --- module verdicts ---------------------------------------------------
    for row in live:
        if row.get("body_verdict") != "MATCH":
            continue
        calls = row.get("calls", [])
        matched = [c for c in calls if c["verdict"] == "MATCH"]
        diverged = [c for c in calls if c["verdict"] == "DIVERGE"]
        unrun = [c for c in calls if c["verdict"] == "RUNNER"]
        row["ncalls"] = len(calls)
        row["nmatched"] = len(matched)
        row["nunrun"] = len(unrun)
        skipped = [f for f in row["oracle"].get("functions", []) if f.get("skipped")]
        row["nfunctions"] = len(row["oracle"].get("functions", []))
        row["nskipped"] = len(skipped)
        if diverged:
            row["verdict"] = "DIVERGED"
            row["detail"] = "%d of %d calls DIVERGED: %s" % (
                len(diverged), len(calls),
                "; ".join("%s%s" % (c["function"], c["detail"]) for c in diverged[:3]))
        elif unrun:
            # The battery did not finish. PARTIAL would be a lie in the one
            # direction that matters: it reads as "the model answered and some
            # answers were wrong", when in fact these calls never ran. An
            # unfinished battery gets its own verdict and its own count.
            row["verdict"] = "INCOMPLETE"
            row["detail"] = ("%d of %d calls never ran (the runner batch did not finish); "
                             "%d of the %d that did agree"
                             % (len(unrun), len(calls), len(matched), len(calls) - len(unrun)))
        elif not calls:
            row["verdict"] = "BODY-ONLY"
            row["detail"] = ("body matched; no drivable public function (%d public, %d skipped)"
                             % (row["nfunctions"], row["nskipped"]))
        elif len(matched) == len(calls):
            row["verdict"] = "VERIFIED"
            row["detail"] = "body + %d/%d calls over %d public function(s)%s" % (
                len(matched), len(calls), row["nfunctions"] - row["nskipped"],
                "; %d function(s) skipped" % row["nskipped"] if row["nskipped"] else "")
        else:
            row["verdict"] = "PARTIAL"
            row["detail"] = "body matched; %d/%d calls agree" % (len(matched), len(calls))
    return rows, {"body_secs": body_secs, "call_secs": call_secs, "ncalls": len(jobs),
                  "runner": " ".join(runner), "scratch": scratch}


CLASS_REFUSAL = "a class whose CREATION"          # Script.lean `runScriptClock`, first admission
NODE_REFUSAL = re.compile(r"unsupported (?:statement|expression) '([^']+)'")


def wall_of(msg):
    """Bucket a refusal message into the wall vocabulary of the censuses
    (`harness/leanpy_survey.py` `census`: `class-creation`, `import`,
    `node:<py_kind>`).

    The message is the model's own words; the bucket exists only so the
    OBSERVED walls can be counted against the census's PREDICTED ones. An
    unrecognised message keeps its own first clause rather than being
    dropped into an 'other' bin — a wall that cannot be named is a wall
    nobody will fix, and this survey's whole product is named walls."""
    if msg.startswith(CLASS_REFUSAL):
        return "class-creation"
    node = NODE_REFUSAL.search(msg)
    if node:
        kind = node.group(1)
        return "import" if kind in ("Import", "ImportFrom") else "node:" + kind
    return "msg:" + msg.split(" (")[0][:60]


def report(rows, stats):
    order = ["VERIFIED", "BODY-ONLY", "PARTIAL", "REFUSED", "DIVERGED", "INCOMPLETE",
             "TIMEOUT", "ORACLE", "RUNNER", "HUNG", "EXTRACT", "MISSING"]
    counts = {}
    for row in rows:
        counts[row.get("verdict", "?")] = counts.get(row.get("verdict", "?"), 0) + 1
    print("=" * 78)
    print("LIBRARY MODE — %d modules, runner %s" % (len(rows), stats["runner"]))
    print("bodies %.1fs, %d battery calls %.1fs" % (stats["body_secs"], stats["ncalls"],
                                                    stats["call_secs"]))
    print("=" * 78)
    for verdict in order:
        if counts.get(verdict):
            print("  %-10s %4d" % (verdict, counts[verdict]))
    for verdict in sorted(set(counts) - set(order)):
        print("  %-10s %4d" % (verdict, counts[verdict]))

    calls = [c for row in rows for c in row.get("calls", [])]
    if calls:
        hist = {}
        for call in calls:
            hist[call["verdict"]] = hist.get(call["verdict"], 0) + 1
        print("\nBATTERY, per call (%d rows)" % len(calls))
        for verdict, n in sorted(hist.items(), key=lambda kv: (-kv[1], kv[0])):
            print("  %-13s %5d" % (verdict, n))
        if hist.get("RUNNER"):
            print("  *** %d calls NEVER RAN: the runner batch did not finish. This "
                  "scoreboard is INCOMPLETE — raise --batch-timeout and re-run. ***"
                  % hist["RUNNER"])

    for title, want in (("VERIFIED", "VERIFIED"), ("BODY-ONLY", "BODY-ONLY"),
                        ("PARTIAL", "PARTIAL"), ("INCOMPLETE — the battery did not finish",
                                                 "INCOMPLETE"), ("DIVERGED", "DIVERGED")):
        sel = [r for r in rows if r.get("verdict") == want]
        if not sel:
            continue
        print("\n%s" % title)
        for row in sel:
            print("  %-28s %s" % (row["module"], row.get("detail", "")))
            if want in ("PARTIAL", "DIVERGED"):
                for call in row.get("calls", []):
                    if call["verdict"] != "MATCH":
                        print("      %-9s %s(%s) %s" % (
                            call["verdict"], call["function"],
                            ", ".join(_pretty(a) for a in call["args"]), call["detail"][:110]))

    print("\nREFUSED, by the construct the model named")
    walls = {}
    for row in rows:
        if row.get("verdict") == "REFUSED":
            walls.setdefault(row.get("observed_wall", "?"), []).append(row["module"])
    for wall, mods in sorted(walls.items(), key=lambda kv: (-len(kv[1]), kv[0])):
        print("  %-34s %4d  %s" % (wall, len(mods), " ".join(sorted(mods)[:6])))

    print("\nRECONCILIATION against the censuses, in three tiers")
    print("  EXACT       the census's first-wall prediction is the wall that fired")
    print("  ORDER       a different wall fired, but the census's wall SET contains it")
    print("  UNPREDICTED the wall that fired is not in the census's set at all — a finding")
    tiers = {"EXACT": [], "ORDER": [], "UNPREDICTED": []}
    for row in rows:
        if row.get("verdict") in (None, "MISSING", "EXTRACT", "HUNG", "RUNNER", "ORACLE"):
            continue
        predicted = row["expected_wall"]
        observed = row.get("observed_wall", "none")
        walls = row["census_walls"]
        if predicted == observed:
            tiers["EXACT"].append((row["module"], predicted, observed))
        elif observed in walls:
            tiers["ORDER"].append((row["module"], predicted, observed))
        else:
            tiers["UNPREDICTED"].append((row["module"], predicted, observed))
    for tier in ("EXACT", "ORDER", "UNPREDICTED"):
        print("  %-12s %4d" % (tier, len(tiers[tier])))
    for tier in ("ORDER", "UNPREDICTED"):
        for module, predicted, observed in tiers[tier][:40]:
            print("    %-11s %-26s census %-24s observed %s"
                  % (tier, module, predicted, observed))
        if len(tiers[tier]) > 40:
            print("    … %d more %s" % (len(tiers[tier]) - 40, tier))
    return counts


def _pretty(v):
    if not isinstance(v, dict):
        return repr(v)
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
        inner = ", ".join(_pretty(x) for x in v["v"])
        return "(%s,)" % inner if t == "tuple" and len(v["v"]) == 1 else \
            ("(%s)" % inner if t == "tuple" else "[%s]" % inner)
    return json.dumps(v)


def battery_bytes(rows):
    """The battery, canonically serialized — what `--determinism` compares.
    Only the INPUTS: the modules, their functions, and the argument tuples
    the harness chose to drive them on."""
    out = []
    for row in sorted(rows, key=lambda r: r["module"]):
        for call in row.get("calls", []):
            out.append([row["module"], call["function"], call["source"], call["args"]])
    return json.dumps(out, sort_keys=True).encode("utf-8")


def main(argv=None):
    parser = argparse.ArgumentParser(prog="library_survey.py")
    parser.add_argument("--corpus", default=MANIFEST)
    parser.add_argument("--build-manifest", action="store_true",
                        help="regenerate the corpus manifest from the censuses and exit")
    parser.add_argument("--only", default=None, metavar="REGEX")
    parser.add_argument("--limit", type=int, default=None)
    parser.add_argument("--fuel", type=int, default=200000,
                        help="fuel for the module BODY (a module's top level is a program)")
    parser.add_argument("--call-fuel", type=int, default=10000,
                        help="fuel per BATTERY CALL. Deliberately modest and separate from "
                             "--fuel: a battery of generated inputs can hand a search function "
                             "an input it will chew on forever, and a loud TIMEOUT row costs one "
                             "verdict while a 200000-fuel one costs the survey.")
    parser.add_argument("--max-calls", type=int, default=8,
                        help="battery rows per public function")
    parser.add_argument("--cpython", default=os.environ.get("LEANPY_CPYTHON")
                        or leanpy_survey.default_oracle())
    parser.add_argument("--oracle-timeout", type=float, default=60.0)
    parser.add_argument("--batch-timeout", type=float, default=900.0,
                        help="wall-clock bound on the BODY batch (the whole corpus at once)")
    parser.add_argument("--module-timeout", type=float, default=120.0,
                        help="wall-clock bound on ONE module's battery. Fuel bounds recursion "
                             "DEPTH, not work, so it cannot serve as a time bound; this can.")
    parser.add_argument("--runner", default=None,
                        help="runner argv (default: tools/leanpy's, with its staleness check). "
                             "A git WORKTREE has no .lake, so point this at the built binary in "
                             "the main checkout rather than provoking a build there.")
    parser.add_argument("--json", dest="json_out", default=None)
    parser.add_argument("--merge", nargs="+", metavar="RESULT.json", default=None,
                        help="print the aggregate scoreboard over several --json results "
                             "and exit. The corpus is surveyed in DISJOINT chunks when one "
                             "process cannot own the machine long enough to finish it; the "
                             "chunks run the same harness on the same battery, so the merged "
                             "rows are the same rows. Overlapping chunks are a loud error — "
                             "a module counted twice is a scoreboard that lies.")
    parser.add_argument("--determinism", action="store_true",
                        help="run the survey twice and compare the battery BYTES")
    opts = parser.parse_args(argv)
    os.chdir(REPO_ROOT)

    if opts.merge:
        rows, seen, secs, ncalls = [], {}, 0.0, 0
        for path in opts.merge:
            with open(path, "r", encoding="utf-8") as f:
                part = json.load(f)
            for row in part["rows"]:
                key = (row["provenance"], row["file"])
                if key in seen:
                    raise SystemExit("library_survey --merge: %s appears in both %s and %s — "
                                     "the chunks are not disjoint" % (row["file"], seen[key], path))
                seen[key] = path
                rows.append(row)
            secs += part["stats"]["body_secs"] + part["stats"]["call_secs"]
            ncalls += part["stats"]["ncalls"]
        counts = report(rows, {"body_secs": secs, "call_secs": 0.0, "ncalls": ncalls,
                               "runner": "merged over %d chunks" % len(opts.merge)})
        if opts.json_out:
            with open(opts.json_out, "w", encoding="utf-8") as f:
                json.dump({"merged": opts.merge, "rows": rows}, f, indent=1,
                          sort_keys=True, default=str)
            print("\nwrote %s" % opts.json_out)
        return 1 if (counts.get("DIVERGED") or counts.get("INCOMPLETE")) else 0

    if opts.build_manifest:
        manifest = build_manifest(MANIFEST)
        print("wrote %s: %d modules (%d from the census, %d in-repo)"
              % (os.path.relpath(MANIFEST, REPO_ROOT), len(manifest["modules"]),
                 sum(1 for m in manifest["modules"] if m["provenance"] == "census:library"),
                 sum(1 for m in manifest["modules"] if m["provenance"].startswith("in-repo"))))
        return 0

    rows, stats = survey(opts)
    counts = report(rows, stats)

    if opts.determinism:
        first = battery_bytes(rows)
        rows2, _ = survey(opts)
        second = battery_bytes(rows2)
        print("\nDETERMINISM: %d battery bytes, %s"
              % (len(first), "IDENTICAL across runs" if first == second else "DIFFERENT — a bug"))
        if first != second:
            return 1

    if opts.json_out:
        with open(opts.json_out, "w", encoding="utf-8") as f:
            json.dump({"cpython": opts.cpython, "stats": stats, "rows": rows},
                      f, indent=1, sort_keys=True, default=str)
        print("\nwrote %s" % opts.json_out)
    # A DIVERGED row is the headline; an INCOMPLETE one means the battery did
    # not finish, and a scoreboard that certifies nothing must not exit 0.
    return 1 if (counts.get("DIVERGED") or counts.get("INCOMPLETE")) else 0


if __name__ == "__main__":
    sys.exit(main())
