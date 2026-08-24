#!/usr/bin/env python3
"""es_score.py — re-derive `es-score`'s summary from its per-test lines.

    es-score 2000 <prelude> <list> | python3 harness/es_score.py --expect 1816
    python3 harness/es_score.py --self-test

TWO INSTRUMENTS, ONE ANSWER. The Lean driver prints its own summary; this
recomputes it from the per-test lines by a different program, so agreement is
evidence and a disagreement is a defect in one of the two. It is also the
gate: `--expect N` fails when the population changes without anyone saying so,
and `--expect-passed N` when the SCORE moves.

THE STATES MUST SUM. Every line carries exactly one token, every token is
known, and `attempted` equals their sum. A scoreboard whose buckets do not add
up to its population has somewhere to hide a test, and the one number that
means anything is then unfalsifiable.

THE FIRST NON-PASS IS REPORTED VERBATIM, IN LOG ORDER — not sorted, not
deduplicated. `sort -u` answers "which distinct outcomes exist"; a reader
after a run asks "what went wrong first", and the two coincide by luck only.
"""

import argparse
import sys

SCORED = ("passed", "failed")
ZEROES = ("refused-construct", "refused-intrinsic", "refused-host", "timeout",
          "threw-other", "prelude-failed", "not-parsed", "not-ingested",
          "runner-error")
TOKENS = SCORED + ZEROES


def parse(lines):
    """-> (rows, driver_summary_lines). Rows are (name, token, detail)."""
    rows, tail, seen_rule = [], [], False
    for raw in lines:
        line = raw.rstrip("\n")
        if line == "----":
            seen_rule = True
            continue
        if seen_rule:
            tail.append(line)
            continue
        if not line.strip():
            continue
        parts = line.split("\t")
        if len(parts) < 2:
            raise SystemExit("es_score: unparseable line (no tab): %r" % line)
        name, token = parts[0], parts[1]
        detail = parts[2] if len(parts) > 2 else ""
        if token not in TOKENS:
            raise SystemExit("es_score: unknown token %r on %r — an unknown state is "
                             "not a zero, it is a hole" % (token, name))
        rows.append((name, token, detail))
    return rows, tail


def summarise(rows):
    counts = {t: 0 for t in TOKENS}
    for _n, t, _d in rows:
        counts[t] += 1
    scored = counts["passed"] + counts["failed"]
    total = sum(counts.values())
    out = ["test262 %d/%d scored  (passed %d, failed %d)"
           % (scored, total, counts["passed"], counts["failed"]),
           "  the zeroes, kept apart: " +
           ", ".join("%s %d" % (t, counts[t]) for t in ZEROES),
           "  states sum to %d" % total]
    first = next(((n, t, d) for n, t, d in rows if t != "passed"), None)
    if first:
        out.append("  FIRST NON-PASS (log order, verbatim): %s  %s  %s" % first)
    return counts, total, out


def self_test():
    ok = True

    def check(label, cond):
        nonlocal ok
        print("  %s %s" % ("ok  " if cond else "FAIL", label))
        if not cond:
            ok = False

    rows, tail = parse(["a\tpassed\t", "b\tfailed\tx !== y",
                        "c\trefused-construct\tclasses", "----", "driver said something"])
    counts, total, out = summarise(rows)
    check("states sum to the row count", total == 3)
    # `scored` is passed PLUS failed: a failure is a verdict, not a zero. The
    # first draft of this case asserted 1/3 and the self-test caught it.
    check("scored counts passed AND failed", "2/3 scored" in out[0])
    check("a refusal is NOT scored", counts["refused-construct"] == 1)
    check("the driver's tail is kept separate", tail == ["driver said something"])
    check("first non-pass is the FIRST, not the first distinct",
          "b  failed  x !== y" in out[-1])
    # a later pass must not displace an earlier non-pass
    rows2, _ = parse(["a\trefused-host\teval", "b\tpassed\t", "c\tfailed\tz"])
    _c2, _t2, out2 = summarise(rows2)
    check("log order, not severity order", "a  refused-host  eval" in out2[-1])
    try:
        parse(["a\tinvented-token\t"])
        check("an unknown token is refused", False)
    except SystemExit:
        check("an unknown token is refused", True)
    try:
        parse(["no tabs here"])
        check("a line with no tab is refused", False)
    except SystemExit:
        check("a line with no tab is refused", True)
    return 0 if ok else 1


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--expect", type=int, help="required attempted count")
    ap.add_argument("--expect-passed", type=int, help="required passed count")
    ap.add_argument("--self-test", action="store_true")
    a = ap.parse_args()
    if a.self_test:
        return self_test()
    rows, tail = parse(sys.stdin)
    counts, total, out = summarise(rows)
    for l in out:
        print(l)
    rc = 0
    if a.expect is not None and total != a.expect:
        print("POPULATION MOVED: attempted %d, expected %d" % (total, a.expect),
              file=sys.stderr)
        rc = 1
    if a.expect_passed is not None and counts["passed"] != a.expect_passed:
        print("SCORE MOVED: passed %d, expected %d" % (counts["passed"], a.expect_passed),
              file=sys.stderr)
        rc = 1
    # The driver's own summary must agree with this one, line for line.
    driver = [l for l in tail if l.strip()]
    mine = [l for l in out]
    if driver and driver[:len(mine)] != mine:
        print("TWO INSTRUMENTS DISAGREE:", file=sys.stderr)
        for d, m in zip(driver, mine):
            if d != m:
                print("  driver: %s\n  scorer: %s" % (d, m), file=sys.stderr)
        rc = 1
    return rc


if __name__ == "__main__":
    sys.exit(main())
