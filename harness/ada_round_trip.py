#!/usr/bin/env python3
"""ada_round_trip.py — the envelope gate, with two independent oracles.

`docs/ada-envelope-schema.md` §5 fixes the rule with FOUR edges, three of
them `docs/backlog.md` §L67's and the fourth Ada's own. This encodes them,
and then does something the SV lane could not: it checks the extractor's
MARKINGS against **the ACAA's own `SUMMARY` tool**, so the half of the
envelope that decides 37.1% of the suite's verdicts is validated by the suite
owner's software rather than by our reading of its documentation.

    python3 harness/ada_round_trip.py <envelope>... --vocab docs/ada-construct-census.json
    python3 harness/ada_round_trip.py --corpus <acats-dir> --summary <path/to/summary>
    python3 harness/ada_round_trip.py --self-test

THE FOUR EDGES, each a measured hazard rather than an anticipated one:

| edge | what it checks | why |
| --- | --- | --- |
| schema version | the envelope's `schema_version` is the one the extractor emits | §L67 |
| top units | regeneration uses `compilation_units`, never a path-derived name | 680 of 4810 ACATS files — one in seven — have a name that is not among their unit names (§L74) |
| source-path spelling | regeneration records the same spelling the envelope did | §L67: absolute-vs-relative made all 18 SV envelopes differ by exactly the string-length delta |
| edition | regeneration uses the envelope's `language_version` | Ada's version pair is forced (spec Ada 2022, suite Ada 2012) |

Plus the family's own binding check: **the node kinds the envelope contains
are a SUBSET of the census's `node_kinds`, and any kind outside it must have
been emitted as an `Unsupported` leaf** — so "what the ingester accepts" and
"what the corpus contains" cannot drift apart silently.

TWO BEHAVIOURAL RULES, adopted verbatim from §L67 because they are what made
that gate honest:

* **it never writes into the repo** — every regeneration goes to a temporary
  directory;
* **an envelope it cannot reproduce is reported WITH the missing path**,
  never passed silently. An envelope whose recorded sources are absolute
  paths into another machine's scratch directory is unreproducible anywhere,
  and saying so is the point.

VERDICT VOCABULARY is `docs/family-architecture.md` §5.1's, not this gate's
own: **MATCH | REFUSE | DIVERGE | TIMEOUT**.  This file said `DIFFER` until
2026-08-22 and was one of the emitters §9.4 measured as drifted; `DIVERGE` is
the law's name and `DIFFER` is gone.  `ERROR`, `SKIP` and `VACUOUS` are NOT
verdicts and are not offered as ones — they are instrument-level outcomes,
which is exactly what §5.3 says a vacuous run is: *"an instrument-level
ERROR, not a verdict — a scoreboard that reports it as MATCH is broken, and
one that reports it as REFUSE is lying about coverage."*

`REFUSE` and `TIMEOUT` do not appear because this gate cannot produce them:
it re-extracts and compares, so there is nothing for the model to decline and
no fuel to exhaust.  When the SCOREBOARD lands (the trace emitter of
`docs/ada-charter.md` §4.4) it carries all four.

Python >= 3.9 plus libadalang (for regeneration).  Exit non-zero on any
DIVERGE or ERROR; SKIP is reported and does not fail the gate.
"""

import argparse
import json
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
EXTRACTOR = os.path.join(HERE, "extractors", "ada", "extract.py")
DEFAULT_VOCAB = os.path.join(HERE, "docs", "ada-construct-census.json")

# The ACAA's SUMMARY tool emits these kinds for the markings; the extractor's
# own names differ in spelling only, and the map is stated rather than assumed.
SUMMARY_TO_ENVELOPE = {"ERROR": "ERROR", "OK": "OK",
                       "OPTIONAL ERROR": "OPTIONAL ERROR",
                       "POSSIBLE ERROR": "POSSIBLE ERROR"}


def node_kinds(node, out):
    if node is None:
        return
    if isinstance(node, list):
        for n in node:
            node_kinds(n, out)
        return
    kind = node.get("kind")
    if kind:
        out.add(kind)
    if kind == "Unsupported":
        out.add("Unsupported:" + str(node.get("node_class")))
    node_kinds(node.get("children"), out)


def regenerate(env, source_root, tmpdir):
    """Re-extract from the envelope's OWN recorded spellings.  Returns
    (envelope | None, note)."""
    paths, names = [], []
    for src in env["source_files"]:
        spelled = src["path"]
        if os.path.isabs(spelled):
            return None, ("SKIP: recorded source path is ABSOLUTE and so is "
                          "unreproducible anywhere: %s" % spelled)
        real = os.path.join(source_root, spelled)
        if not os.path.exists(real):
            alt = find_by_basename(source_root, os.path.basename(spelled))
            if alt is None:
                return None, ("SKIP: recorded source not found under %s: %s"
                              % (source_root, spelled))
            real = alt
        paths.append(real)
        names.append(spelled)
    out = os.path.join(tmpdir, "regen.json")
    cmd = [sys.executable, EXTRACTOR] + paths + ["-o", out,
           "--vocab", "none",
           "--language-version", env["language_version"],
           "--profile-id", env["profile_id"],
           "--allow-diagnostics"]
    for n in names:
        cmd += ["--source-name", n]
    run = subprocess.run(cmd, capture_output=True, text=True, timeout=900)
    if run.returncode != 0:
        return None, "ERROR: re-extraction failed: %s" % run.stderr.strip()[:200]
    with open(out) as fh:
        return json.load(fh), ""


_INDEX = {}


def find_by_basename(root, base):
    if root not in _INDEX:
        idx = {}
        for dirpath, _, filenames in os.walk(root):
            for f in filenames:
                idx.setdefault(f.lower(), os.path.join(dirpath, f))
        _INDEX[root] = idx
    return _INDEX[root].get(base.lower())


def check(env, source_root, vocab, tmpdir):
    """One envelope -> (verdict, [notes])."""
    notes = []

    # EDGE 1 — schema version.
    if env.get("schema_version") != "ada-0.1":
        return "DIVERGE", ["schema_version is %r, not 'ada-0.1'"
                          % env.get("schema_version")]
    # EDGE 4 — edition.  An envelope with no edition is not a program.
    if not env.get("language_version"):
        return "DIVERGE", ["no language_version — the edition is part of the "
                          "program (docs/ada-envelope-schema.md §0.1)"]

    # THE VOCABULARY CHECK — binding, per the schema's §3.
    if vocab is not None:
        seen = set()
        for cu in env["compilation_units"]:
            node_kinds(cu.get("decl"), seen)
        stray = sorted(k for k in seen
                       if not k.startswith("Unsupported")
                       and k != "Unsupported" and k not in vocab)
        if stray:
            return "DIVERGE", ["node kinds outside the census vocabulary and "
                              "not emitted as Unsupported: %s"
                              % ", ".join(stray[:8])]

    regen, note = regenerate(env, source_root, tmpdir)
    if regen is None:
        return note.split(":")[0], [note]

    # EDGE 2 — top units, read from the envelope and not from a path.
    a = [(u["name"], u["kind"], u["order"]) for u in env["compilation_units"]]
    b = [(u["name"], u["kind"], u["order"]) for u in regen["compilation_units"]]
    if a != b:
        notes.append("compilation_units differ: %r vs %r" % (a[:4], b[:4]))
    # EDGE 3 — the recorded spelling.
    if ([s["path"] for s in env["source_files"]]
            != [s["path"] for s in regen["source_files"]]):
        notes.append("source_files spelling differs")
    for key in ("markings", "unsupported_count", "language_version",
                "profile_id"):
        if env.get(key) != regen.get(key):
            notes.append("%s differs" % key)
    if json.dumps(env["compilation_units"], sort_keys=True) != \
            json.dumps(regen["compilation_units"], sort_keys=True):
        notes.append("compilation_units payload differs")
    return ("MATCH" if not notes else "DIVERGE"), notes


_SUM_SEQ = [0]


def summary_markings(summary_exe, source, tmpdir):
    """The ACAA's own SUMMARY tool's view of a source's markings.

    TWO TRAPS, both measured, both of which make the tool fail QUIETLY while
    printing its normal progress messages — the same species as §L69's CRLF
    finding, and the reason this function is longer than it looks:

    1. **It will not overwrite an existing output file.**  It leaves the
       stale content in place and exits without complaint, so reusing one
       output path across a multi-file envelope reads the FIRST file's rows
       for every later file.  Unique path per call, removed first.

    2. **A basename longer than 12 characters raises
       `ADA.STRINGS.LENGTH_ERROR`.**  The ACATS convention is 8 characters
       plus a 1-3 character extension and the tool has a fixed buffer for it.
       Measured exactly: `B3710011XY.A` (12) works, `lf-B3710011.A` (13)
       raises.  So the copy KEEPS the original basename and gets its own
       subdirectory instead of a prefix — renaming it was how this gate came
       to report four markings "only ours" on three files whose markings the
       tool had found exactly."""
    import csv
    _SUM_SEQ[0] += 1
    workdir = os.path.join(tmpdir, "sum%04d" % _SUM_SEQ[0])
    os.makedirs(workdir, exist_ok=True)
    lf = os.path.join(workdir, os.path.basename(source))
    with open(source, "rb") as fh:
        data = fh.read()
    with open(lf, "wb") as fh:
        fh.write(data.replace(b"\r\n", b"\n"))
    out = os.path.join(workdir, "sum.csv")
    if os.path.exists(out):
        os.remove(out)
    run = subprocess.run([summary_exe, lf, out], capture_output=True,
                         text=True, timeout=300)
    if not os.path.exists(out):
        return None, "SUMMARY produced nothing: %s" % (
            (run.stdout + run.stderr).strip()[:160])
    with open(out) as fh:
        rows = list(csv.DictReader(fh))
    marks = [(r["Kind"], int(r["Start Line"]), int(r["Start Pos"]),
              int(r["End Line"]), int(r["End Pos"]))
             for r in rows if r["Kind"] in SUMMARY_TO_ENVELOPE]
    return sorted(marks), ""


def check_markings(env, summary_exe, source_root, tmpdir):
    """Cross-check the extractor's markings against the ACAA's own tool.

    This is the strongest validation available for the half of the envelope
    that decides 37.1% of the suite's verdicts: the suite OWNER's software is
    the oracle, not our reading of its User's Guide.

    EVERY source file is checked, not just the first.  The first version
    compared only `file == 0` and then reported `MATCH  0 marking(s) agree`
    on a four-file envelope carrying twelve markings — a VACUOUS pass, which
    `docs/family-architecture.md` §5.3 says must never count as agreement.
    An envelope with no markings anywhere is reported VACUOUS, not MATCH."""
    total, agreed, notes = 0, 0, []
    for index, src in enumerate(env["source_files"]):
        spelled = src["path"]
        real = os.path.join(source_root, spelled)
        if not os.path.exists(real):
            real = find_by_basename(source_root, os.path.basename(spelled))
        if real is None:
            return "SKIP", "source not found for the cross-check: %s" % spelled
        theirs, note = summary_markings(summary_exe, real, tmpdir)
        if theirs is None:
            return "ERROR", "%s: %s" % (spelled, note)
        ours = sorted((m["kind"], m["line"], m["col"], m["end_line"],
                       m["end_col"])
                      for m in env["markings"] if m["file"] == index
                      and m["kind"] in SUMMARY_TO_ENVELOPE)
        total += max(len(ours), len(theirs))
        if ours == theirs:
            agreed += len(ours)
            continue
        only_ours = [m for m in ours if m not in theirs]
        only_theirs = [m for m in theirs if m not in ours]
        notes.append("%s: %d only ours %r, %d only theirs %r"
                     % (spelled, len(only_ours), only_ours[:2],
                        len(only_theirs), only_theirs[:2]))
    if notes:
        return "DIVERGE", "; ".join(notes)
    if total == 0:
        return "VACUOUS", ("no markings on either side across %d source(s) — "
                           "nothing was compared, so this is not agreement"
                           % len(env["source_files"]))
    return "MATCH", ("%d marking(s) across %d source(s) agree with the ACAA's "
                     "SUMMARY" % (agreed, len(env["source_files"])))


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("envelopes", nargs="*")
    ap.add_argument("--source-root", default=".",
                    help="where the envelopes' recorded spellings resolve")
    ap.add_argument("--vocab", default=DEFAULT_VOCAB)
    ap.add_argument("--summary", help="the ACAA's built SUMMARY executable; "
                                      "enables the markings cross-check")
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()

    if args.self_test:
        return self_test()
    if not args.envelopes:
        sys.exit("ada_round_trip: at least one envelope is required")

    vocab = None
    if args.vocab and args.vocab != "none":
        if not os.path.exists(args.vocab):
            sys.exit("ada_round_trip: vocabulary not found: %s" % args.vocab)
        with open(args.vocab) as fh:
            vocab = set(json.load(fh)["node_kinds"])

    tally = {"MATCH": 0, "DIVERGE": 0, "ERROR": 0, "SKIP": 0}
    mtally = {"MATCH": 0, "DIVERGE": 0, "ERROR": 0, "SKIP": 0, "VACUOUS": 0}
    bad = False
    with tempfile.TemporaryDirectory() as tmpdir:
        for path in args.envelopes:
            if not os.path.exists(path):
                print("ERROR  %s: no such envelope" % path)
                tally["ERROR"] += 1
                bad = True
                continue
            with open(path) as fh:
                env = json.load(fh)
            verdict, notes = check(env, args.source_root, vocab, tmpdir)
            tally[verdict] = tally.get(verdict, 0) + 1
            print("%-6s %s%s" % (verdict, os.path.basename(path),
                                 ("  | " + "; ".join(notes)) if notes else ""))
            if verdict in ("DIVERGE", "ERROR"):
                bad = True
            if args.summary:
                mv, mnote = check_markings(env, args.summary, args.source_root,
                                           tmpdir)
                mtally[mv] = mtally.get(mv, 0) + 1
                print("       markings %-6s %s" % (mv, mnote))
                if mv in ("DIVERGE", "ERROR"):
                    bad = True
    print("round-trip: " + ", ".join("%s %d" % (k, v)
                                     for k, v in sorted(tally.items())))
    if args.summary:
        print("markings vs the ACAA's SUMMARY: "
              + ", ".join("%s %d" % (k, v) for k, v in sorted(mtally.items())))
    return 1 if bad else 0


def self_test():
    """The gate must FAIL a tampered envelope, or it is decoration.  Each
    edge is broken in turn and the gate must name it."""
    ok = True
    base = {"schema_version": "ada-0.1", "language_version": "Ada2012",
            "profile_id": "p", "source_files": [{"path": "x.ada"}],
            "compilation_units": [{"name": "X", "kind": "PackageDecl",
                                   "order": 0,
                                   "decl": {"kind": "PackageDecl"}}],
            "markings": [], "unsupported_count": 0}

    def verdict(env, vocab=None):
        with tempfile.TemporaryDirectory() as t:
            return check(env, t, vocab, t)[0]

    cases = [
        ("a wrong schema version is caught",
         verdict({**base, "schema_version": "ada-9.9"}), "DIVERGE"),
        ("a missing edition is caught",
         verdict({**base, "language_version": ""}), "DIVERGE"),
        ("a node kind outside the vocabulary is caught",
         verdict(base, {"SomethingElse"}), "DIVERGE"),
        ("a kind INSIDE the vocabulary passes the vocabulary check",
         verdict(base, {"PackageDecl"}), "SKIP"),
        ("an Unsupported leaf is NOT a vocabulary violation",
         verdict({**base, "compilation_units": [
             {**base["compilation_units"][0],
              "decl": {"kind": "Unsupported", "node_class": "TaskTypeDecl"}}]},
                 {"PackageDecl"}), "SKIP"),
        ("an ABSOLUTE recorded path is SKIPped with the path named",
         verdict({**base, "source_files": [{"path": "/abs/x.ada"}]},
                 {"PackageDecl"}), "SKIP"),
    ]
    for name, got, want in cases:
        if got != want:
            ok = False
        print("%s %-56s got %r want %r"
              % ("ok " if got == want else "FAIL", name, got, want))
    print("self-test:", "PASSED" if ok else "FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
