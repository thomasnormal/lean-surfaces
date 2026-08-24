#!/usr/bin/env python3
"""es_score_corpus.py — choose the scoreboard's POPULATION, and pin it by content.

    python3 harness/es_score_corpus.py --tests <test262> --acorn-dir <dir> \
        --manifest <out.jsonl> [--envelopes <dir>] [-o docs/es-scoreboard-corpus.json]
    python3 harness/es_score_corpus.py --check docs/es-scoreboard-corpus.json --manifest <m>
    python3 harness/es_score_corpus.py --self-test

**A SAMPLE RULE MUST NAME ITS POPULATION.**  "1,834 tests" is not a
measurement until the 1,834 are identified, because the next run can quietly
score a different 1,834 and report the same shape.  So the rule below is
executable, and its output is pinned by a DIGEST OVER CONTENT — the sha256 of
the sorted `<relpath> <sha256>` lines.  Re-derive the population and the digest
either matches or the corpus moved; nothing in between.

THE RULE, in full:

  a test/language/*.js file, excluding `_FIXTURE` and module-code/import/export
  AND it parses as a Script
  AND its frontmatter has no `module`, `async` or `CanBlock*` flag
  AND it is not a `negative:` test
  AND every node kind it uses is STATED or PARTIAL per harness/es_coverage.py
  AND every free identifier is one the mandatory prelude defines
      (Test262Error, assert, compareArray) or a value global the tier binds
      (undefined, NaN, Infinity)

The last clause is the one that moves: it is the realm's frontier, not the
evaluator's.  Widening it is the realm inch, and the digest is what makes that
widening visible instead of silent.

WHY THE FULL LIST IS NOT IN `docs/`.  It is ~1,800 lines of generated data
whose every byte is derivable from the rule plus the pinned test262 commit.
`docs/` carries the RULE, the commit, the count and the digest; the list goes
beside the run.  A digest that can be recomputed is a stronger pin than a list
nobody diffs.
"""

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PRELUDE_DEFINES = {"Test262Error", "assert", "compareArray", "$DONOTEVALUATE"}
VALUE_GLOBALS = {"undefined", "NaN", "Infinity"}
OUT_OF_SLICE_FLAGS = {"module", "async", "CanBlockIsTrue", "CanBlockIsFalse"}


def stated_kinds():
    """The kinds the evaluator STATES or PARTIALLY states, from the instrument
    rather than from a list kept here — MEAS-28: one definition, one place."""
    out = subprocess.run([sys.executable, os.path.join(REPO, "harness", "es_coverage.py"),
                          "--json"], capture_output=True, text=True, cwd=REPO)
    if out.returncode not in (0, 1):
        raise SystemExit("es_score_corpus: es_coverage.py failed:\n" + out.stderr)
    cov = json.loads(out.stdout)
    lean = cov["kinds"]["stated"] + cov["kinds"]["partial"]
    return {k[0].upper() + k[1:] for k in lean}


def admit(row, kinds):
    """The rule, as one function, so `--self-test` can exercise every clause."""
    if not row.get("parsed"):
        return False, "not-parsed"
    if row.get("negative"):
        return False, "negative-test"
    if set(row.get("flags") or []) & OUT_OF_SLICE_FLAGS:
        return False, "out-of-slice-flag"
    if not set(row["k"]) <= kinds:
        return False, "kind-outside-the-evaluator"
    if not set(row["free"]) <= PRELUDE_DEFINES | VALUE_GLOBALS:
        return False, "needs-an-intrinsic"
    return True, "admitted"


def digest(entries):
    """sha256 over the sorted `<relpath> <sha256>` lines. Content, not order."""
    body = "".join("%s %s\n" % (e["path"], e["sha256"]) for e in sorted(entries, key=lambda e: e["path"]))
    return hashlib.sha256(body.encode()).hexdigest()


def rev(path):
    r = subprocess.run(["git", "-C", path, "log", "-1", "--format=%H %cI"],
                       capture_output=True, text=True)
    if r.returncode != 0 or not r.stdout.strip():
        raise SystemExit("es_score_corpus: %s has no recoverable revision — a corpus "
                         "whose state cannot be quoted is an INPUT FAULT (§5.4a)" % path)
    return r.stdout.strip()


def build(args):
    tests = os.path.abspath(args.tests)
    lang = os.path.join(tests, "test", "language")
    if not os.path.isdir(lang):
        raise SystemExit("es_score_corpus: %s is not a test262 checkout" % tests)
    files = []
    for root, _dirs, names in os.walk(lang):
        parts = os.path.relpath(root, os.path.join(tests, "test")).split(os.sep)
        if len(parts) > 1 and parts[1] in ("module-code", "import", "export"):
            continue
        for n in sorted(names):
            if n.endswith(".js") and "_FIXTURE" not in n:
                files.append(os.path.join(root, n))
    files.sort()
    listing = os.path.join(args.workdir, "es-slice-files.txt")
    os.makedirs(args.workdir, exist_ok=True)
    open(listing, "w").write("\n".join(files) + "\n")
    probe = os.path.join(REPO, "harness", "es", "slice_probe.mjs")
    jsonl = os.path.join(args.workdir, "es-slice-probe.jsonl")
    r = subprocess.run(["node", probe, listing, jsonl, args.acorn], capture_output=True,
                       text=True)
    if r.returncode != 0:
        raise SystemExit("es_score_corpus: slice_probe failed:\n" + r.stderr)

    kinds = stated_kinds()
    entries, rejected = [], {}
    for line in open(jsonl):
        row = json.loads(line)
        ok, why = admit(row, kinds)
        if not ok:
            rejected[why] = rejected.get(why, 0) + 1
            continue
        rel = os.path.relpath(row["f"], tests)
        entries.append({"path": rel,
                        "sha256": hashlib.sha256(open(row["f"], "rb").read()).hexdigest()})
    entries.sort(key=lambda e: e["path"])
    with open(args.manifest, "w") as f:
        for e in entries:
            f.write(json.dumps(e) + "\n")
    doc = {
        "schema": "es-scoreboard-corpus-1",
        "test262": rev(tests),
        "population_rule": [
            "test/language/*.js, excluding _FIXTURE and module-code/import/export",
            "parses as a Script",
            "no module/async/CanBlock* frontmatter flag",
            "not a negative: test",
            "every node kind STATED or PARTIAL per harness/es_coverage.py",
            "every free identifier defined by the prelude or bound as a value global",
        ],
        "admitted": len(entries),
        "rejected": rejected,
        "manifest_sha256": digest(entries),
    }
    if args.out:
        open(args.out, "w").write(json.dumps(doc, indent=2, sort_keys=True) + "\n")
        print("wrote %s" % args.out)
    print("population: %d admitted, rejected %s" % (len(entries), rejected))
    print("manifest sha256: %s" % doc["manifest_sha256"])
    return 0


def check(args):
    doc = json.load(open(args.check))
    entries = [json.loads(l) for l in open(args.manifest)]
    got = digest(entries)
    if got != doc["manifest_sha256"]:
        print("CORPUS MOVED: manifest sha256 %s, pinned %s" % (got, doc["manifest_sha256"]),
              file=sys.stderr)
        return 1
    if len(entries) != doc["admitted"]:
        print("CORPUS MOVED: %d entries, pinned %d" % (len(entries), doc["admitted"]),
              file=sys.stderr)
        return 1
    print("corpus: %d tests, sha256 %s — unchanged" % (len(entries), got))
    return 0


def self_test():
    kinds = {"Program", "ExpressionStatement", "CallExpression", "Identifier", "Literal",
             "MemberExpression"}
    base = {"parsed": True, "negative": False, "flags": [],
            "k": ["Program", "ExpressionStatement", "CallExpression", "Identifier", "Literal",
                  "MemberExpression"],
            "free": ["assert"]}
    cases = [
        (dict(base), True, "a plain assert test is admitted"),
        (dict(base, parsed=False), False, "a file that did not parse"),
        (dict(base, negative=True), False, "a negative: test"),
        (dict(base, flags=["module"]), False, "a module-flagged test"),
        (dict(base, flags=["onlyStrict"]), True, "an unrelated flag does not exclude"),
        (dict(base, k=base["k"] + ["ClassBody"]), False, "a kind outside the evaluator"),
        (dict(base, free=["Object"]), False, "a test needing an intrinsic"),
        (dict(base, free=["undefined", "NaN", "Infinity"]), True, "value globals are bound"),
    ]
    ok = True
    for row, want, label in cases:
        got, why = admit(row, kinds)
        flag = "ok  " if got == want else "FAIL"
        if got != want:
            ok = False
        print("  %s %-42s -> %s" % (flag, label, why))
    a = [{"path": "b", "sha256": "2"}, {"path": "a", "sha256": "1"}]
    b = [{"path": "a", "sha256": "1"}, {"path": "b", "sha256": "2"}]
    if digest(a) != digest(b):
        print("  FAIL digest depends on order"); ok = False
    else:
        print("  ok   digest is order-independent")
    if digest(a) == digest([{"path": "a", "sha256": "1"}, {"path": "b", "sha256": "X"}]):
        print("  FAIL digest ignores content"); ok = False
    else:
        print("  ok   digest changes when a file's content changes")
    return 0 if ok else 1


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--tests"); ap.add_argument("--acorn", help="path to a fetched acorn ESM entry point")
    ap.add_argument("--manifest"); ap.add_argument("-o", "--out")
    ap.add_argument("--workdir", default="/tmp")
    ap.add_argument("--check"); ap.add_argument("--self-test", action="store_true")
    a = ap.parse_args()
    if a.self_test:
        return self_test()
    if a.check:
        return check(a)
    if not (a.tests and a.manifest and a.acorn):
        ap.error("--tests, --acorn and --manifest are required")
    return build(a)


if __name__ == "__main__":
    sys.exit(main())
