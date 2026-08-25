#!/usr/bin/env python3
"""c_divergence_probe.py — the C tier's guards for docs/c-declared-divergences.json.

SCRIPT SHAPE (`harness/divergence_register.py`, PROBE SHAPES): the register
names this file, the checker runs it with `--json`, and reads each guard's
`held`.

**BOTH GUARDS READ A COMMITTED ARTIFACT, and that is the whole design.**
`docs/c-torture-scoreboard.json` is the §9.0 number written down —
`harness/c_torture_score.py --emit` produces it from a `lake exe
c-torture-run` log, and it lists every `failed` test BY NAME, because a count
cannot say WHICH. So this probe runs on any machine, with no corpus, no
toolchain and no lock, and still asks the two questions the register exists
to ask:

  c_div_1_still_divergent   is 20021127-1.c STILL failing?  A divergence that
                            has been silently fixed leaves a stale
                            declaration, and a stale declaration is a false
                            claim about the tier that reads as diligence.
                            Note the shape of the trap: this row's own
                            retirement path is RECLASSIFICATION into the
                            `oracle-tests-compiler` state, and the day that
                            lands, this guard goes red — which is correct.
                            The row must be retired deliberately, not drained.

  c_div_1_has_not_widened   is the scoreboard's `failed` count still no larger
                            than the number of LIVE rows?  A second failing
                            test with no second row is the register describing
                            a smaller fact than the tree contains, which is
                            the failure no reader notices.

The probe deliberately does NOT re-derive the verdict: re-running the corpus
would need the GPL cache, clang and a Lean build, none of which a checker
should assume. It reads what the tenure published. That is the same division
`c_torture_score.py` already makes against the Lean driver — the number is
produced once, under the lock, and everything downstream reads it.
"""
import argparse
import json
import os
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SCOREBOARD = os.path.join(REPO, "docs", "c-torture-scoreboard.json")
REGISTER = os.path.join(REPO, "docs", "c-declared-divergences.json")
C_DIV_1_TEST = "20021127-1.c"


def load(path):
    with open(path, encoding="utf-8") as fh:
        return json.load(fh)


def guards():
    out = {}
    if not os.path.isfile(SCOREBOARD):
        msg = ("docs/c-torture-scoreboard.json is missing — the number was "
               "never published, so neither question can be asked")
        return {"c_div_1_still_divergent": {"held": False, "detail": msg},
                "c_div_1_has_not_widened": {"held": False, "detail": msg}}
    sb = load(SCOREBOARD)
    failed = list(sb.get("failed_tests") or [])
    n_failed = int((sb.get("counts") or {}).get("failed", len(failed)))

    held = C_DIV_1_TEST in failed
    out["c_div_1_still_divergent"] = {
        "held": held,
        "detail": ("%s is still `failed` on the committed scoreboard"
                   % C_DIV_1_TEST) if held else
                  ("%s is NO LONGER failing (failed_tests=%r). If that is the "
                   "oracle-tests-compiler reclassification, RETIRE the row; if "
                   "it is a silent fix, the declaration is now false."
                   % (C_DIV_1_TEST, failed))}

    live = len(load(REGISTER).get("rows") or []) if os.path.isfile(REGISTER) else 0
    ok = n_failed <= live
    out["c_div_1_has_not_widened"] = {
        "held": ok,
        "detail": ("scoreboard failed=%d, live register rows=%d (pinned <=)"
                   % (n_failed, live)) if ok else
                  ("scoreboard failed=%d EXCEEDS the %d live register row(s): "
                   "%r. A failing test with no row is a divergence nobody "
                   "declared." % (n_failed, live, failed))}
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--json", action="store_true")
    a = ap.parse_args()
    g = guards()
    for name in sorted(g):
        print("%-28s %-5s %s" % (name, "ok" if g[name]["held"] else "FAIL",
                                 g[name]["detail"]))
    if a.json:
        print(json.dumps(g, indent=1, sort_keys=True))
    ok = all(v["held"] for v in g.values())
    print("\nc_divergence_probe: %s" % ("PASS" if ok else "FAIL"))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
