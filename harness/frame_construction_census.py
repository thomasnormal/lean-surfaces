#!/usr/bin/env python3
"""frame_construction_census.py — WHO CONSTRUCTS EACH GENERATOR FRAME.

    python3 harness/frame_construction_census.py [--json]

**Why this exists.** Three `GenFrame` arms in the TRUNK's `execGen` refuse with
a message saying the trunk never builds that frame. §5.2's ruling
(family-architecture, 2026-08-24) settled what such an arm owes: where the
impossibility cannot be discharged at the TYPE level — and here it cannot, the
frames live inside `Obj.generator` on a shared heap, so narrowing means indexing
the heap by presentation — refusal-form wins, **but the documentation stops
being what carries the claim.**

> *"The trunk never constructs this frame" is MEASURABLE: a census over
> construction sites.* Once gated, the arm is no longer BELIEVED unreachable
> but MEASURED unreachable.

**AND THE CENSUS CORRECTED THE QUESTION THAT ORDERED IT.** The pyc lane asked
for a ruling about "three unreachable refusals". Only TWO are unreachable:
`enumDict` is built by `enumFrame`, which the TRUNK's own `enumerate` arm calls
(§3c-i-c ruling (c) chose that deliberately), so its step arm is a LIVE path.
That row is pinned here as a POSITIVE expectation, so the correction cannot be
quietly lost the way the belief was.

**What is measured.** A frame reaches the trunk iff something the trunk
evaluates constructs it. For `iterDict`/`enumDict` the construction is inside a
shared pure worker (`iterFrame`/`enumFrame`) that LIVES in a trunk file, so the
file it is written in proves nothing — what decides it is WHO CALLS the worker.
That distinction is exactly what the enumDict correction turned on.

Heuristic and its guard: occurrences inside backticks (prose), inside `--`
comments, and inside Lean name-quotes (` `` `) are not calls. The heuristic is
not trusted on its own — every count is PINNED, so any drift fails the census
and a human re-derives rather than the number silently moving.

Exit 0 = every expectation held. Exit 1 = a drift (report says which).
Python 3.9 compatible.
"""

import argparse
import glob
import json
import os
import re
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
# THE FILE SET IS THE MEASUREMENT'S REAL CONTENT, and getting it wrong is how
# the first draft of this census reported two false drifts. A frame reaches the
# trunk iff a trunk EVALUATOR constructs it. `ClockErase`/`PayloadBlind`/`Obs`
# mention the same workers while REASONING about the trunk, and a construction
# written inside a shared worker proves nothing about who calls it -- the very
# distinction the enumDict correction turned on.
EVAL_TRUNK = [os.path.join(REPO, "LeanModels/Python", f)
              for f in ("Semantics.lean", "Script.lean")]
EVAL_REBUILD = sorted(glob.glob(os.path.join(REPO, "LeanModels/Python/Monadic/*.lean")))
ALL_EVAL = EVAL_TRUNK + EVAL_REBUILD


def _code_lines(path):
    """Lines with prose stripped: Lean name-quotes, backticked spans and `--`
    comments removed. A line that is only prose becomes empty."""
    out = []
    for n, line in enumerate(open(path, encoding="utf-8"), 1):
        s = re.sub(r"``[A-Za-z_][A-Za-z0-9_.]*", " ", line)   # Lean name literal
        s = re.sub(r"`[^`]*`", " ", s)                         # backticked prose
        s = re.sub(r"--.*$", " ", s)                           # line comment
        out.append((n, s))
    return out


def calls_of(fn, files):
    """Files in which `fn` appears as a CALL (applied to an argument)."""
    hits = {}
    pat = re.compile(r"\b%s\b\s*[\(\w←]" % re.escape(fn))
    for f in files:
        for n, s in _code_lines(f):
            if re.search(r"\bdef\s+%s\b" % re.escape(fn), s):
                continue                                       # its own definition
            if pat.search(s):
                hits.setdefault(os.path.relpath(f, REPO), []).append(n)
    return hits


# PINNED at 2026-08-24. A change in either direction is a census failure: the
# point is not the number but that nobody can move it without being seen.
EXPECT = [
    ("iterDict", ["iterFrame"], 0,
     "the trunk has no `iter` arm at all, so nothing it evaluates reaches the "
     "worker - the refusal in its execGen arm is MEASURED unreachable"),
    ("enumDict", ["enumFrame"], 1,
     "POSITIVE, and it is the correction: the trunk's own `enumerate` arm calls "
     "the shared worker, so this frame IS built by the trunk and its step arm "
     "is a LIVE path, not an unreachable one"),
    ("forDict", ["genInitCont", "K.forDict", "S.forDict"], 0,
     "built through the Kont/SKont field and (since the PEP 289 fix) through "
     "`genInitCont`, which lives in a trunk FILE and has only rebuild callers - "
     "file location proves nothing, the caller does"),
]


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--json", action="store_true")
    opts = ap.parse_args(argv)
    rc = 0
    report = {}

    print("FRAME CONSTRUCTION CENSUS — who builds each GenFrame, measured")
    for frame, routes, want_trunk, why in EXPECT:
        callers = {}
        for worker in routes:
            for k, v in calls_of(worker, ALL_EVAL).items():
                callers.setdefault(k, []).extend(v)
        trunk = {k: v for k, v in callers.items() if "/Monadic/" not in k}
        rebuild = {k: v for k, v in callers.items() if "/Monadic/" in k}
        ok = len(trunk) == want_trunk
        rc |= 0 if ok else 1
        report[frame] = {"routes": routes, "trunk_callers": trunk,
                         "rebuild_callers": rebuild, "expected_trunk": want_trunk,
                         "ok": ok}
        print("  %-9s via %-34s trunk callers: %d (pinned %d) %s"
              % (frame, "/".join(routes), len(trunk), want_trunk,
                 "ok" if ok else "DRIFT"))
        print("      trunk:   %s" % (", ".join(sorted(trunk)) or "(none)"))
        print("      rebuild: %s" % (", ".join(sorted(rebuild)) or "(none)"))
        print("      %s" % why)

    if opts.json:
        print(json.dumps(report, indent=1, sort_keys=True))
    print("\nframe_construction_census: %s" % ("OK" if rc == 0 else "DRIFT"))
    return rc


if __name__ == "__main__":
    sys.exit(main())
