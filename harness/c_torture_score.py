#!/usr/bin/env python3
"""c_torture_score.py — read `c-torture-run`'s lines, produce §9.0's number.

TWO INSTRUMENTS, ONE ANSWER — the M1 discipline, one level up.  The Lean
driver prints its own summary; this recomputes it from the per-test lines
by a different program, so agreement is evidence and a disagreement is a
defect in one of the two.  It is also the gate: `--expect N/total` fails
the build when the number moves without anyone saying so.

TWO REPORTING RULES, both learned the hard way elsewhere and both
EXECUTED in `--selftest` rather than described.

1. THE FIRST FAILURE IS PRINTED VERBATIM, IN LOG ORDER.  Not sorted, not
   deduplicated, not "a representative failure".  `sort -u` over failures
   answers *"which distinct failures exist"*; a reader after a red run
   asks *"what went wrong first"*, and the two coincide only by luck.  A
   summary that silently answers the other question is worse than none,
   because it looks like an answer.

2. THE ZEROES ARE NOT THE SAME ZERO.  `not-fetched`, `not-parsed`,
   `refused-*` and `timeout` are all "0 scored" and they are four
   different facts about four different subsystems — the fetch, the
   frontend, the model's frontier, and the fuel bound.  Pooling them
   makes the scoreboard unfalsifiable: it can no longer tell *"the model
   declined"* from *"nobody ran it"*, which is the only distinction that
   says whether a rung would move the number.
"""
import argparse, sys

SCORED = ("passed", "failed")
ZEROES = ("refused-unsupported", "refused-libc", "refused-ub", "timeout",
          "not-ingested", "not-parsed", "runner-error", "not-fetched")
TOKENS = SCORED + ZEROES


def parse(lines):
    rows, seen_rule = [], False
    for raw in lines:
        line = raw.rstrip("\n")
        if line == "----":
            seen_rule = True
            continue
        if seen_rule or not line or "\t" not in line:
            continue
        parts = line.split("\t")
        name, token = parts[0], parts[1]
        detail = parts[2] if len(parts) > 2 else ""
        if token not in TOKENS:
            raise SystemExit("c_torture_score: unknown verdict token %r on %r" % (token, name))
        rows.append((name, token, detail))
    return rows


def summarise(rows):
    counts = {t: 0 for t in TOKENS}
    first_failure = None
    for name, token, detail in rows:            # LOG ORDER, no sort, no dedup
        counts[token] += 1
        if token == "failed" and first_failure is None:
            first_failure = (name, token, detail)
    scored = counts["passed"] + counts["failed"]
    return counts, scored, len(rows), first_failure


def render(counts, scored, total, first_failure):
    out = ["gcc.c-torture %d/%d scored  (passed %d, failed %d)"
           % (scored, total, counts["passed"], counts["failed"]),
           "  the zeroes, kept apart: " + ", ".join(
               "%s %d" % (t, counts[t]) for t in ZEROES)]
    if first_failure is None:
        out.append("  first failure: none")
    else:
        out.append("  FIRST FAILURE (log order, verbatim): %s  %s  %s" % first_failure)
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("log", nargs="?", help="c-torture-run output (default: stdin)")
    ap.add_argument("--expect", help="N/total — fail if the number moved")
    ap.add_argument("--emit", help="write the scoreboard as JSON to this path")
    ap.add_argument("--selftest", action="store_true")
    a = ap.parse_args()
    if a.selftest:
        return selftest()
    lines = open(a.log).readlines() if a.log else sys.stdin.readlines()
    rows = parse(lines)
    counts, scored, total, ff = summarise(rows)
    for l in render(counts, scored, total, ff):
        print(l)
    if a.emit:
        # THE NUMBER AS A COMMITTED ARTIFACT.  A §9.0 figure that lives only in
        # a tenure log cannot be read by anything offline -- not by a reviewer,
        # and not by `harness/c_divergence_probe.py`, which has to ask "is this
        # test still failing?" on a machine with no corpus.  Every `failed` row
        # is listed by NAME, because a count cannot say WHICH.
        import json as _json
        _json.dump({
            "note": ("Written by harness/c_torture_score.py --emit, from a "
                     "`lake exe c-torture-run` log.  The pin is "
                     "docs/c-torture-pin.json.  This file is the tier's §9.0 "
                     "number as a second artifact: correcting the instrument "
                     "corrects the next run, and the published figure is "
                     "corrected where it was published."),
            "corpus": "gcc.c-torture/execute",
            "scored": scored, "total": total,
            "counts": {k: counts[k] for k in TOKENS},
            "failed_tests": [n for n, t, _ in rows if t == "failed"],
        }, open(a.emit, "w"), indent=1, sort_keys=True)
        open(a.emit, "a").write("\n")
        print("c_torture_score: scoreboard written to %s" % a.emit)
    if a.expect:
        want = a.expect.strip()
        got = "%d/%d" % (scored, total)
        if got != want:
            print("c_torture_score: THE NUMBER MOVED — expected %s, got %s. "
                  "If that is the landing, say so and update the gate." % (want, got),
                  file=sys.stderr)
            return 1
    return 0


def selftest():
    ok = True

    def check(name, got, want):
        nonlocal ok
        good = got == want
        ok = ok and good
        print("  %-56s %s" % (name, "ok" if good else "FAIL got=%r want=%r" % (got, want)))

    # RULE 1: log order, and the sort-u trap.  `zz` fails first; `aa` fails
    # later with the same detail.  Sorting would report `aa`; deduplicating
    # would collapse them and report whichever survived.
    log = ["zz.c\tfailed\treached abort\n",
           "mm.c\trefused-unsupported\tswitch\n",
           "aa.c\tfailed\treached abort\n",
           "----\n", "ignored summary line\n"]
    _, _, _, ff = summarise(parse(log))
    check("first failure is the FIRST, not the smallest", ff[0], "zz.c")
    check("the summary block after ---- is not counted", len(parse(log)), 3)
    dedup = sorted({(t, d) for _, t, d in parse(log) if t == "failed"})
    check("dedup would have collapsed two failures to one", len(dedup), 1)

    # RULE 2: four zeroes, four numbers, and `scored` counts neither.
    log2 = ["a\tnot-fetched\t\n", "b\tnot-parsed\tK&R definition\n",
            "g\tnot-ingested\tspan: field 'col': Natural number expected\n",
            "h\trunner-error\tcannot read envelope\n",
            "c\trefused-unsupported\tswitch\n", "d\trefused-libc\tprintf\n",
            "e\trefused-ub\tsignedOverflow\n", "f\ttimeout\t\n"]
    counts, scored, total, ff = summarise(parse(log2))
    check("eight absences, zero scored", (scored, total), (0, 8))
    check("not-ingested is NOT pooled with not-parsed",
          (counts["not-ingested"], counts["not-parsed"]), (1, 1))
    check("not-fetched is its own number", counts["not-fetched"], 1)
    check("not-parsed is its own number", counts["not-parsed"], 1)
    check("refused-libc is not pooled with refused-ub",
          (counts["refused-libc"], counts["refused-ub"]), (1, 1))
    check("no failure to report", ff, None)
    rendered = "\n".join(render(counts, scored, total, ff))
    check("every zero-state is named in the render",
          all(t in rendered for t in ZEROES), True)

    # scored = passed + failed, and `failed` is a SCORE
    counts3, scored3, total3, _ = summarise(parse(
        ["p\tpassed\t\n", "q\tfailed\treached abort\n", "r\ttimeout\t\n"]))
    check("scored counts failed as a score", (scored3, total3), (2, 3))

    # an unknown token is refused, never silently bucketed
    try:
        parse(["x\tsomething-else\t\n"])
        check("unknown token refused", "accepted", "refused")
    except SystemExit:
        check("unknown token refused", "refused", "refused")

    print("c_torture_score --selftest:", "ok" if ok else "FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
