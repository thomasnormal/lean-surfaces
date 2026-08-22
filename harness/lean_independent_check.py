#!/usr/bin/env python3
"""The Lean tier's INDEPENDENT-CHECKER gate (M1 inch 6).

Runs an independent Lean typechecker over compiled `.olean` environments and
scores each module with the family's verdicts.

THE VERDICT MAPPING, and it is the reason this instrument is short but not
trivial. **Every `.olean` already carries the C++ kernel's implicit accept** — it
exists only because the kernel admitted every declaration in it. So the oracle's
expected value is free and is always "accept", and:

    MATCH    the independent checker also accepted.
    DIVERGE  the independent checker REJECTED something the C++ kernel admitted.
             This is the family's highest-stakes DIVERGE (`docs/lean-tier-charter.md`
             §3.2): it means a soundness bug in ONE OF THE TWO, and it is not
             automatically ours.
    REFUSE   the checker declined for a reason that is not a verdict — an
             unsupported construct, a native-reduction axiom it will not model
             (`lean4lean` hard-refuses `reduceBool`/`reduceNat`), or a module it
             cannot replay. Never scored as agreement.
    TIMEOUT  wall-clock exhaustion. Never conflated with REFUSE.

WHAT A GREEN RUN DOES AND DOES NOT BUY. It buys: a second implementation, written
by different people from a different starting point, agrees that these
environments typecheck. It does NOT buy: that the shared type theory is
consistent (§0 — Gödel), nor true independence (`lean4lean`'s own README says it
"is not really an independent implementation", being derived from the C++
kernel). Both caveats are stamped into the output so a consumer cannot read the
number without them.

`--maybe` implements the family's CI helper contract: checker present => run,
absent => SKIP loudly and exit 0. A gate that is a permanent silent skip is a
check pretending.

Usage:
    lean_independent_check.py --checker-dir DIR --modules Init.Core [...]
    lean_independent_check.py --checker-dir DIR --modules ... --maybe --gate -o OUT
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import time
from pathlib import Path


class CensusRefusal(Exception):
    """The instrument declines, loudly.  An input fault, never a finding."""


# lean4lean's own refusal texts.  A REFUSE must be distinguished from a DIVERGE
# by reading what the checker said, never by assuming a nonzero exit is a bug.
REFUSAL_MARKERS = (
    "does not support",           # e.g. "lean4lean does not support 'reduceBool' reduction"
    "loose bound variables",      # the Lean-import limitation of digama0/lean4lean#17
    "unsupported",
)

# A module the checker cannot LOCATE is not a verdict about anything — it is a
# bad module list. Scoring it would MANUFACTURE a DIVERGE, and DIVERGE is the
# family's zero-tolerance invariant (§5.1): a manufactured one either halts a
# lane chasing a non-bug or trains it to tolerate the row. So the whole run
# refuses instead. Found by running the fixture: a deliberately bogus module
# scored DIVERGE before this existed.
INPUT_FAULT_MARKERS = (
    "could not find any oleans",
    "unknown module",
    "unknown package",
)


def classify(exit_code: int, out: str, err: str, timed_out: bool) -> tuple[str, str]:
    if timed_out: return "TIMEOUT", "wall-clock exhausted"
    blob = (out + "\n" + err)
    low = blob.lower()
    if exit_code == 0: return "MATCH", ""
    for m in INPUT_FAULT_MARKERS:
        if m in low:
            line = next((l.strip() for l in blob.splitlines() if m in l.lower()), m)
            raise CensusRefusal(f"the checker could not locate a module: {line[:200]}")
    for m in REFUSAL_MARKERS:
        if m in low:
            line = next((l.strip() for l in blob.splitlines() if m in l.lower()), m)
            return "REFUSE", line[:300]
    first = next((l.strip() for l in blob.splitlines() if l.strip()), "(no output)")
    return "DIVERGE", first[:300]


def run(checker_dir: Path, modules: list[str], timeout: int, lean_path: str | None) -> dict:
    if not modules: raise CensusRefusal("no modules given")
    if not checker_dir.is_dir(): raise CensusRefusal(f"missing --checker-dir: {checker_dir}")
    if not (checker_dir / "lakefile.toml").is_file() and not (checker_dir / "lakefile.lean").is_file():
        raise CensusRefusal(f"--checker-dir is not a lake package: {checker_dir}")

    env = dict(os.environ)
    if lean_path: env["LEAN_PATH"] = lean_path + ":" + env.get("LEAN_PATH", "")

    # §5.4a — the checker's commit is not decoration: `checker_commit` is what
    # makes a verdict re-derivable, and lean4lean's agreement means nothing
    # without saying WHICH lean4lean.  The previous version swallowed every
    # failure and stamped `""`, which reads cleaner than the truth.  A checker
    # whose revision cannot be recovered is an INPUT FAULT (§5.2).
    try:
        r = subprocess.run(["git", "-C", str(checker_dir), "rev-parse", "HEAD"],
                           capture_output=True, text=True, timeout=30)
    except (OSError, subprocess.SubprocessError) as exc:
        raise CensusRefusal(f"cannot run git in {checker_dir}: {exc} — the checker "
                            f"revision is part of the result (§5.4a), not a stamp on it")
    if r.returncode != 0 or not r.stdout.strip():
        raise CensusRefusal(f"no git revision for --checker-dir {checker_dir} "
                            f"(exit {r.returncode}): {(r.stderr or '').strip()[:200]} — "
                            f"§5.4a forbids reporting verdicts against a checker whose "
                            f"commit cannot be named")
    rev = r.stdout.strip()

    rows = []
    for m in modules:
        cmd = ["nice", "-n", "10", "lake", "exe", "lean4lean", m]
        t0 = time.time()
        timed_out = False
        try:
            p = subprocess.run(cmd, cwd=str(checker_dir), capture_output=True,
                               text=True, timeout=timeout, env=env)
            code, out, err = p.returncode, p.stdout, p.stderr
        except subprocess.TimeoutExpired:
            code, out, err, timed_out = -1, "", "", True
        dt = round(time.time() - t0, 1)
        verdict, detail = classify(code, out, err, timed_out)
        rows.append({"module": m, "verdict": verdict, "exit_code": code,
                     "seconds": dt, "detail": detail})

    counts: dict[str, int] = {}
    for r_ in rows: counts[r_["verdict"]] = counts.get(r_["verdict"], 0) + 1

    return {
        "schema": "lean-independent-check/1",
        "checker": "lean4lean",
        "checker_commit": rev,
        "oracle": "the C++ kernel's implicit accept, carried by every .olean",
        "caveats": [
            "A green run does NOT establish consistency of Lean's type theory (Godel; "
            "see docs/lean-tier-charter.md section 0).",
            "lean4lean's own README states it is derived from the C++ kernel and 'is not "
            "really an independent implementation', so agreement is weaker evidence than "
            "agreement with a from-scratch checker.",
        ],
        "verdicts": dict(sorted(counts.items())),
        "modules_checked": len(rows),
        "rows": rows,
    }


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--checker-dir", required=True, type=Path)
    ap.add_argument("--modules", nargs="+", required=True)
    ap.add_argument("--lean-path")
    ap.add_argument("--timeout", type=int, default=2400)
    ap.add_argument("-o", "--output", type=Path)
    ap.add_argument("--compare", type=Path)
    ap.add_argument("--maybe", action="store_true",
                    help="checker absent => SKIP loudly and exit 0 (the family's `maybe` contract)")
    ap.add_argument("--gate", action="store_true", help="exit 1 on any DIVERGE")
    args = ap.parse_args(argv)

    built = (args.checker_dir / ".lake" / "build" / "bin" / "lean4lean")
    if args.maybe and not built.is_file():
        print(f"SKIP: no lean4lean binary at {built} — checker not built on this host", file=sys.stderr)
        return 0

    try:
        result = run(args.checker_dir, args.modules, args.timeout, args.lean_path)
    except CensusRefusal as exc:
        print(f"REFUSE: {exc}", file=sys.stderr)
        return 2

    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.compare:
        if not args.compare.is_file():
            print(f"REFUSE: missing baseline: {args.compare}", file=sys.stderr); return 2
        old = json.loads(args.compare.read_text())
        # Timings are not part of the contract; compare verdicts only.
        def strip(d):
            d = json.loads(json.dumps(d))
            for r_ in d.get("rows", []): r_.pop("seconds", None)
            return d
        if strip(old) == strip(result):
            print(f"ok: verdicts match {args.compare}"); return 0
        for key in sorted(set(old) | set(result)):
            if strip({"rows": old.get("rows", []), key: old.get(key)}) != \
               strip({"rows": result.get("rows", []), key: result.get(key)}):
                print(f"DRIFT: {key}", file=sys.stderr)
        return 1

    if args.output:
        args.output.write_text(text, encoding="utf-8"); print(f"wrote {args.output}", file=sys.stderr)
    else:
        sys.stdout.write(text)

    d = result["verdicts"].get("DIVERGE", 0)
    if args.gate and d:
        print(f"GATE FAILED: {d} DIVERGE — a soundness bug in the checker or the kernel", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
