#!/usr/bin/env python3
"""monadic_gate.py — the MONADIC REBUILD's acceptance gate, bucketed by arm.

    python3 harness/monadic_gate.py [--runner CMD] [--cases harness/cases.json]
                                    [--no-build] [--json OUT]

Runs `harness/cases.json` through BOTH interpreters — the trunk
(`LeanModels/Python/Semantics.lean`) and the monadic rebuild
(`LeanModels/Python/Monadic/`) — through the SAME `leanmodels-run --batch`
machinery, and reports:

  1. **PARITY** — the count of rows on which the two interpreters answer
     IDENTICALLY. That number, at 1394 with 0 divergences, is the gate.
  2. **THE FRONTIER, BUCKETED BY ARM** — every row the rebuild refuses with a
     `monadic-rebuild:` message, grouped by the arm named in that message and
     ranked by how many rows it blocks. This is the burn-down list, and it is
     what makes the remaining work rankable rather than a single number.
  3. **DIVERGENCES** — rows where the two interpreters disagree and the
     rebuild's answer is NOT a `monadic-rebuild:` refusal. **These are the
     findings.** A divergence is a bug in one of the two, adjudicated by
     CPython, and the tool prints CPython's answer beside both so the
     adjudication can be made on the spot. Any divergence is a non-zero exit.

WHY BUCKETING IS THE POINT. The rebuild's own frontier is spelled
`monadic-rebuild: arm not yet transliterated: <arm>` precisely so it can never
be confused with a TIER refusal — a statement about Python. Without that split a
gate report would say "N rows fail" and could not say whether the rebuild is
missing a feature or getting Python wrong. With it, the two questions are
answered separately and only the second one is alarming.

Python 3.9 compatible.
"""

import argparse
import collections
import json
import os
import subprocess
import sys

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def _reexec_under_pinned_cpython():
    """RE-EXEC BEFORE IMPORTING `diff_test`, and the order is the whole point.

    `diff_test.py` re-execs ITSELF into the pinned 3.9 oracle at import time
    (`os.execv(exe, [exe, __file__] + argv)`), because it runs the oracle
    IN-PROCESS. Importing it from here under any other Python would therefore
    hand the process to `diff_test.py` and silently abandon this tool — the
    gate would print a diff_test table and never run the comparison. Doing the
    same re-exec FIRST means that by the time the import happens we are already
    on the pin, and `diff_test`'s own guard returns early.

    Found by reading, not by a failing run: on a 3.9 box the bug is invisible.
    """
    if os.environ.get("LEANPY_NO_REEXEC"):
        return
    want = os.environ.get("LEANPY_CPYTHON") or "python3.9"
    if sys.version_info[:2] == (3, 9) and not os.environ.get("LEANPY_CPYTHON"):
        return
    from shutil import which
    exe = which(want)
    if exe is None:
        print("harness/monadic_gate.py: WARNING the pinned oracle %r is not "
              "installed; comparing against %s instead"
              % (want, sys.version.split()[0]), file=sys.stderr)
        return
    if os.path.realpath(exe) == os.path.realpath(sys.executable):
        return
    os.environ["LEANPY_NO_REEXEC"] = "1"
    os.execv(exe, [exe, os.path.abspath(__file__)] + sys.argv[1:])


_reexec_under_pinned_cpython()

sys.path.insert(0, os.path.join(REPO_ROOT, "harness"))

import diff_test  # noqa: E402  (same directory; reuses its canonical forms)

NOT_YET = "monadic-rebuild: arm not yet transliterated: "


def arm_of(result):
    """The arm a `monadic-rebuild:` refusal names, or None."""
    if result.get("status") != "unsupported":
        return None
    msg = result.get("msg") or ""
    if not msg.startswith(NOT_YET):
        return None
    arm = msg[len(NOT_YET):]
    # Collapse the interpolated tail so `builtin: zip()` and `builtin: map()`
    # bucket separately but `call: live module binding 'foo'` does not explode
    # into one bucket per name.
    for prefix in ("call: live module binding",
                   "call: statically-poisoned module binding",
                   "call: class instantiation",
                   "call: namedtuple construction",
                   "call: method call"):
        if arm.startswith(prefix):
            return prefix + " …"
    return arm


def show(result):
    """`diff_test.pretty` collapses every refusal to the bare word
    `unsupported`, which is right for its own table and wrong here: the whole
    point of this tool is WHICH refusal. So the message rides along.

    THE SAME BLINDNESS IS WHY THIS TOOL EXISTS. `diff_test.py` compares an
    `expect: "unsupported"` row by STATUS ALONE, so a rebuild `notYet` lands on
    a whitelisted row as WHITELISTED — a false pass that would flatter the
    rebuild by up to the whitelist's whole size. Comparing the two interpreters
    row by row, message included, is the only reading that cannot do that, and
    it is the number the gate reports."""
    if result.get("status") == "unsupported":
        return "unsupported: " + (result.get("msg") or "")
    return diff_test.pretty(result)


def run_side(runner_cmd, jobs, label):
    """All jobs through one runner process; returns the result list in order."""
    out = [None] * len(jobs)

    def on_result(i, r):
        out[i] = r
        if (i + 1) % 200 == 0 or i + 1 == len(jobs):
            print("  %s: %d/%d" % (label, i + 1, len(jobs)), file=sys.stderr)

    diff_test.run_lean_batch(runner_cmd, jobs, on_result)
    return out


# CAPABILITY OPENINGS — divergences the no-backwards-compat RULING CREATED.
#
# The rebuild is not required to be a clone. When a capability opens on the
# monadic definition only, the trunk keeps a refuse arm and the two
# interpreters answer differently ON PURPOSE. Without this table the gate
# would call that a finding and exit non-zero, so a ruled inch could not land
# green — and the fix must not be to switch the gate off.
#
# THE TABLE CANNOT SILENCE A BUG, and that is its whole design: a row counts
# as OPENED only when the rebuild's answer MATCHES CPYTHON. If the rebuild
# diverges from CPython the row is a FINDING no matter what is written here,
# because the adjudicator is the oracle, never this dict.
OPENED = {
    "iter_dict": "inch 3a — the live dict cursor opens on the monadic "
                 "definition only (docs/backlog/python-completeness.md, "
                 "2026-08-23-pycomplete-5)",
}


def main(argv=None):
    ap = argparse.ArgumentParser(prog="monadic_gate.py")
    ap.add_argument("--cases", default=os.path.join("harness", "cases.json"))
    ap.add_argument("--runner", default="lake exe leanmodels-run")
    ap.add_argument("--no-build", action="store_true")
    ap.add_argument("--json", default=None)
    opts = ap.parse_args(argv)

    os.chdir(REPO_ROOT)
    runner_cmd = opts.runner.split()

    # THE AMENDMENT 14 CONTRACT (tools/triad.sh, 4d32526): the TENURE builds the
    # runner explicitly and exports LS_RUNNER_PREBUILT=1 to its gates. A gate must
    # therefore never build the tree itself. Building it here defeated
    # `--build-target` narrowing outright, and — worse — surfaced an unrelated
    # build failure as a GATE failure, which is the flattering-direction lie
    # §5.4a names: the number would have been attributed to the wrong thing.
    # Unset (a bare invocation outside a tenure) builds ONLY the runner, never
    # the tree.
    if not opts.no_build and not os.environ.get("LS_RUNNER_PREBUILT"):
        if subprocess.run(["lake", "build", "leanmodels-run"],
                          cwd=REPO_ROOT).returncode != 0:
            print("error: `lake build leanmodels-run` failed", file=sys.stderr)
            return 2

    with open(opts.cases, "r", encoding="utf-8") as f:
        cases = json.load(f)

    # The CPython oracle, for adjudicating divergences.
    calls, jobs, oracle = [], [], []
    for case in cases:
        src, fname = case["file"], case["function"]
        json_path = os.path.splitext(src)[0] + ".json"
        mod = diff_test.load_module(src)
        fuel = case.get("fuel")
        clock_spec = case.get("clock")
        for args in case["args"]:
            call = "%s(%s)" % (
                fname, ", ".join(repr(diff_test.from_typed(a)) for a in args))
            if clock_spec is None:
                cpy, trace = diff_test.run_cpython(mod, fname, args), None
            else:
                cpy, trace = diff_test.run_cpython_clock(
                    mod, fname, args, clock_spec)
            calls.append(call)
            oracle.append(cpy)
            jobs.append(diff_test.batch_job(json_path, fname, args, fuel, trace))

    print("running %d rows through BOTH interpreters" % len(jobs),
          file=sys.stderr)
    trunk = run_side(runner_cmd, jobs, "trunk")
    mono = run_side(runner_cmd + ["--monadic"], jobs, "monadic")

    same = 0
    buckets = collections.Counter()
    diverged = []
    opened = []
    for call, cpy, t, m in zip(calls, oracle, trunk, mono):
        if t == m:
            same += 1
            continue
        arm = arm_of(m)
        if arm is not None:
            buckets[arm] += 1
        elif call.split("(", 1)[0] in OPENED and m == cpy:
            # A RULED CAPABILITY OPENING, not a finding — see OPENED.
            opened.append((call, cpy, t, m))
        else:
            diverged.append((call, cpy, t, m))

    total = len(jobs)
    bar = "-" * 78
    print(bar)
    print("MONADIC REBUILD GATE  (harness/monadic_gate.py)")
    print(bar)
    print("rows                      %d" % total)
    if not total:
        # An EMPTY corpus is not a pass. A gate that divides by its own row
        # count crashes here, and a gate that printed "100%" would be worse —
        # it would report vacuous agreement as the acceptance number.
        print("NO ROWS — the corpus is empty; this is not a result", file=sys.stderr)
        return 2
    print("PARITY with the trunk     %d  (%.1f%%)" % (same, 100.0 * same / total))
    print("frontier (`notYet`)       %d  in %d arms" % (sum(buckets.values()),
                                                        len(buckets)))
    print("capability OPENINGS       %d  (ruled; monadic agrees with CPython)"
          % len(opened))
    print("DIVERGENCES               %d%s" % (len(diverged),
                                              "   <-- FINDINGS" if diverged else ""))
    print(bar)
    if buckets:
        print("THE BURN-DOWN LIST — rows blocked, by arm:")
        for arm, n in buckets.most_common():
            print("  %5d  %s" % (n, arm))
        print(bar)
    if opened:
        print("CAPABILITY OPENINGS — the trunk refuses, the rebuild runs, and")
        print("CPython agrees with the rebuild:")
        for call, cpy, t, m in opened:
            print("  %-34s %s" % (call, OPENED[call.split("(", 1)[0]]))
            print("      cpython/monadic : %s" % show(cpy))
            print("      trunk           : %s" % show(t))
        print(bar)
    if diverged:
        print("DIVERGENCES — adjudicated by CPython, which is printed first:")
        for call, cpy, t, m in diverged[:40]:
            print("  %s" % call)
            print("      cpython : %s" % show(cpy))
            print("      trunk   : %s" % show(t))
            print("      monadic : %s" % show(m))
        if len(diverged) > 40:
            print("  … and %d more" % (len(diverged) - 40))
        print(bar)

    if opts.json:
        with open(opts.json, "w", encoding="utf-8") as f:
            json.dump({"rows": total, "parity": same,
                       "frontier": dict(buckets),
                       "opened": [{"call": c, "cpython": p, "trunk": t,
                                   "monadic": m} for c, p, t, m in opened],
                       "divergences": [{"call": c, "cpython": p,
                                        "trunk": t, "monadic": m}
                                       for c, p, t, m in diverged]},
                      f, indent=2, sort_keys=True)
        print("wrote %s" % opts.json)

    return 1 if diverged else 0


if __name__ == "__main__":
    sys.exit(main())
