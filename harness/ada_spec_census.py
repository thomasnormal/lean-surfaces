#!/usr/bin/env python3
"""ada_spec_census.py — measure the Ada Reference Manual's own rule apparatus.

The Ada tier is the first in the family whose SPEC classifies every one of its
own paragraphs.  The ARM (ISO/IEC 8652) divides each subclause under a fixed
set of headings — Legality Rules, Static Semantics, Dynamic Semantics, Bounded
(Run-Time) Errors, Erroneous Execution, Implementation Permissions, ... — and
`docs/ada-charter.md` maps those headings onto the family's refusal taxonomy.
A map drawn from memory would be a guess, so this counts them.

    python3 harness/ada_spec_census.py <dir-of-RM-*.TXT> [-o out.json]
    python3 harness/ada_spec_census.py <dir> --compare docs/ada-spec-census.json
    python3 harness/ada_spec_census.py --self-test

INPUT is the ARM's own plain-text rendering (`RM-TOC.TXT`, `RM-01.TXT` ...
`RM-Q.TXT`), which the ACAA publishes.  Nothing is vendored: point the
instrument at an unpacked copy.  The edition is read out of the text, never
assumed.

WHAT IS MEASURED, and by what rule — because every number here is a
line-shape decision and a reader must be able to check it:

* the SUBCLAUSE list comes from the document's own table of contents, not
  from a guess about line shapes.  This matters: at column 0 a subclause
  heading (`9.1 Task Units`) and a dotted paragraph number (`28.1  Storage_
  Error is propagated ...`) are the same shape, and both occur.  The TOC
  decides, and the instrument then REFUSES if a clause file does not contain
  exactly the headings the TOC promised, in order — so the two halves of the
  document check each other;
* a CATEGORY heading is a CENTERED line (indent >= 10) whose text is one of
  the headings ARM 1.1.2 lists;
* a PARAGRAPH is a line at column 0 beginning with a paragraph number,
  optionally `/<version>` — the ARM's own numbering — that is not a subclause
  heading.  Paragraphs are attributed to the category heading most recently
  seen in the same subclause; text before any category heading is that
  subclause's INTRO.

The paragraph counts are the decision-relevant half: how many headings say
"Bounded (Run-Time) Errors" matters far less than how much of the standard
lives under them.

REFUSAL PATHS.  A missing directory refuses.  A directory with no `RM-*.TXT`
refuses.  A missing `RM-TOC.TXT` refuses — without it the instrument is
guessing.  A clause file whose headings disagree with the TOC refuses, by
name.  A run that attributes ZERO paragraphs refuses: an empty census is an
instrument fault, never a finding.

Python >= 3.9, stdlib only.  Deterministic: sorted output, byte-identical on
a double run.
"""

import argparse
import collections
import hashlib
import json
import os
import re
import sys

# The headings ARM 1.1.2 ("Structure") lists, in ITS order.  `NOTES` is in
# that list but the plain-text rendering inlines notes as `NOTE n` paragraph
# text rather than emitting a heading, so it is carried here and measures
# zero; the instrument reports what it finds, not what it hoped.
CATEGORIES = [
    "Syntax",
    "Name Resolution Rules",
    "Legality Rules",
    "Static Semantics",
    "Post-Compilation Rules",
    "Dynamic Semantics",
    "Bounded (Run-Time) Errors",
    "Erroneous Execution",
    "Implementation Requirements",
    "Documentation Requirements",
    "Metrics",
    "Implementation Permissions",
    "Implementation Advice",
    "Usage",
    "NOTES",
    "Examples",
]

# ARM 1.1.2 partitions the document itself: the CORE is clauses 1-13 plus
# annexes A, B and J; C, D, E, F, G and H are the Specialized Needs Annexes;
# the rest are informative.  Conformance is defined separately for the core
# and for each SNA (ARM 1.1.3), so a tier that scopes itself to the core is
# making a claim the standard already has a word for.
CORE = [str(n) for n in range(1, 14)] + ["A", "B", "J"]
SNA = ["C", "D", "E", "F", "G", "H"]

TOC = "RM-TOC.TXT"
# Files with no rule structure.  Excluded by name and reported, so the
# exclusion is auditable rather than silent.
NON_CLAUSE = {"RM-TTL.TXT", TOC, "RM-IDX.TXT", "RM-00.TXT", "RM-LIB.TXT"}

ID = r"(?:\d+(?:\.\d+)*)|(?:[A-Z](?:\.\d+)*)"
PARA = re.compile(r"^(\d[\d.]*)(?:/(\d+))?(?:\s|$)")
TOC_LINE = re.compile(r"^(\s*)(" + ID + r")\.?(\s+\S.*)?$")
HEAD = re.compile(r"^(" + ID + r")\s+(\S.*?)\s*$")
INTRO = "(intro)"


def read_toc(directory):
    """The document's own subclause list, per clause, in order."""
    path = os.path.join(directory, TOC)
    if not os.path.exists(path):
        sys.exit("ada_spec_census: no %s in %s — the table of contents is "
                 "what tells a subclause heading from a paragraph number; "
                 "without it this instrument would be guessing"
                 % (TOC, directory))
    order, cur = collections.OrderedDict(), None
    with open(path, encoding="latin-1") as fh:
        for raw in fh:
            line = raw.rstrip("\r\n")
            m = TOC_LINE.match(line)
            if not m:
                continue
            indent, ident = len(m.group(1)), m.group(2)
            if indent == 0 and "." not in ident:
                cur = ident
                order.setdefault(cur, [])
            elif indent > 0 and cur is not None:
                order[cur].append(ident)
    if not order:
        sys.exit("ada_spec_census: %s yielded no clauses — instrument fault"
                 % TOC)
    return order


def clause_of(name):
    """`RM-04.TXT` -> `4`, `RM-A.TXT` -> `A`."""
    stem = re.sub(r"(?i)^RM-|\.TXT$", "", name)
    return stem.lstrip("0") or stem


def scan(path, cid, expected):
    """One clause file -> (subclause rows, per-category paragraph counter).

    `expected` is the TOC's ordered id list for this clause.  A heading is
    recognized only when it is the NEXT id the TOC promises, which makes the
    heading/paragraph ambiguity decidable and turns a drifted document into a
    loud failure rather than a quiet miscount."""
    rows, cats, pending = [], collections.Counter(), list(expected)
    cur = {"id": cid, "title": "(clause intro)", "paras": 0, "categories": []}
    heading, seen = INTRO, []
    with open(path, encoding="latin-1") as fh:
        for raw in fh:
            line = raw.rstrip("\r\n")
            text = line.strip()
            if not text:
                continue
            indent = len(line) - len(line.lstrip())
            if indent >= 10 and text in CATEGORIES:
                heading = text
                if heading not in seen:
                    seen.append(heading)
                continue
            if indent == 0:
                m = HEAD.match(line)
                if m and pending and m.group(1) == pending[0]:
                    cur["categories"] = seen
                    rows.append(cur)
                    cur = {"id": pending.pop(0), "title": m.group(2),
                           "paras": 0, "categories": []}
                    heading, seen = INTRO, []
                    continue
            if PARA.match(line):
                cur["paras"] += 1
                cats[heading] += 1
    cur["categories"] = seen
    rows.append(cur)
    if pending:
        sys.exit("ada_spec_census: %s is missing %d heading(s) the table of "
                 "contents promises, first %s — the document and this "
                 "instrument disagree, which is a fault, not a finding"
                 % (os.path.basename(path), len(pending), pending[0]))
    return rows, cats


def edition(directory):
    """Read the edition out of the text rather than assuming it."""
    path = os.path.join(directory, "RM-00.TXT")
    if not os.path.exists(path):
        return None
    with open(path, encoding="latin-1") as fh:
        head = fh.read(4000)
    m = re.search(r"ISO/IEC 8652:(\d+)", head)
    n = re.search(r"informally known as Ada (\d+)", head)
    return {"international_standard": m.group(0) if m else None,
            "informal_name": ("Ada " + n.group(1)) if n else None}


def build(directory):
    toc = read_toc(directory)
    names = sorted(f for f in os.listdir(directory)
                   if re.fullmatch(r"RM-.+\.TXT", f, re.IGNORECASE))
    if not names:
        sys.exit("ada_spec_census: no RM-*.TXT files under %s" % directory)
    used = [n for n in names if n.upper() not in NON_CLAUSE]
    files, subclauses, cats = [], [], collections.Counter()
    for name in used:
        cid = clause_of(name)
        if cid not in toc:
            sys.exit("ada_spec_census: %s is clause %r, which the table of "
                     "contents does not list" % (name, cid))
        path = os.path.join(directory, name)
        rows, fcats = scan(path, cid, toc[cid])
        total = sum(r["paras"] for r in rows)
        if total == 0:
            sys.exit("ada_spec_census: %s yielded ZERO paragraphs — the "
                     "instrument does not understand this file, which is a "
                     "fault and not a finding" % name)
        with open(path, "rb") as fh:
            digest = hashlib.sha256(fh.read()).hexdigest()
        files.append({"file": name, "clause": cid, "sha256": digest,
                      "subclauses": len(rows) - 1, "paragraphs": total})
        for r in rows:
            r["file"] = name
        subclauses.extend(rows)
        cats.update(fcats)
    total = sum(f["paragraphs"] for f in files)
    if total == 0:
        sys.exit("ada_spec_census: zero paragraphs overall — instrument fault")
    carrying = collections.Counter()
    for r in subclauses:
        for c in r["categories"]:
            carrying[c] += 1

    def group(clauses):
        want = {n for n in clauses}
        keep = {f["file"] for f in files if f["clause"] in want}
        sub = [r for r in subclauses if r["file"] in keep]
        cnt = collections.Counter()
        for name in keep:
            cid = clause_of(name)
            _, fc = scan(os.path.join(directory, name), cid, toc[cid])
            cnt.update(fc)
        return {"clauses": sorted(want & {f["clause"] for f in files}),
                "paragraphs": sum(r["paras"] for r in sub),
                "subclauses": sum(f["subclauses"] for f in files
                                  if f["clause"] in want),
                "by_category": {c: cnt.get(c, 0) for c in CATEGORIES}}

    ed = edition(directory)
    return {
        "instrument": "harness/ada_spec_census.py",
        # `docs/family-architecture.md` §1.5: the edition TOKEN, derived from
        # the document rather than asserted, so pointing this instrument at
        # another edition reports that edition.
        "language": "Ada",
        "language_version": (ed or {}).get("informal_name", "").replace(" ", "")
                            or None,
        "frontend": "none — the ARM's own plain-text rendering",
        "edition": ed,
        "files_censused": files,
        "files_skipped": sorted(set(names) - set(used)),
        "clauses_total": len(used),
        "paragraphs_total": total,
        "subclauses_total": sum(f["subclauses"] for f in files),
        "paragraphs_by_category": {c: cats.get(c, 0) for c in CATEGORIES},
        "paragraphs_uncategorized": cats.get(INTRO, 0),
        "core": group(CORE),
        "specialized_needs_annexes": group(SNA),
        "core_clauses_1_13": group([str(n) for n in range(1, 14)]),
        "subclauses_carrying_category": {c: carrying.get(c, 0)
                                         for c in CATEGORIES},
        "subclauses": [{"file": r["file"], "id": r["id"], "title": r["title"],
                        "paragraphs": r["paras"], "categories": r["categories"]}
                       for r in subclauses],
    }


SELF_TEST_TOC = """\
                              Table of Contents

9. Tasks and Synchronization
    9.1 Task Units
    9.2 Task Execution
"""

SELF_TEST_CLAUSE = """\
                          9   Tasks and Synchronization


1   The rules for this clause.


9.1 Task Units


1   An intro paragraph.


                                   Syntax

2       task_type_declaration ::= task type


                               Legality Rules

3/5 A legality rule.

4   A second legality rule.


                          Bounded (Run-Time) Errors

5/2 A bounded error.


                             Erroneous Execution

6   An erroneous case.

28.1    A dotted paragraph number, which is NOT a heading.


9.2 Task Execution


1   Only an intro here.
"""


def self_test():
    """A tool that answered the same way on every input would print the same
    headline, so the shapes it must distinguish are exercised on a fixture
    built to make it answer.  The last Erroneous Execution paragraph is the
    heading/paragraph ambiguity in miniature."""
    import tempfile
    ok = True
    with tempfile.TemporaryDirectory() as d:
        with open(os.path.join(d, TOC), "w") as fh:
            fh.write(SELF_TEST_TOC)
        with open(os.path.join(d, "RM-09.TXT"), "w") as fh:
            fh.write(SELF_TEST_CLAUSE)
        out = build(d)
        cat = out["paragraphs_by_category"]
        checks = [
            ("paragraphs_total", out["paragraphs_total"], 9),
            ("subclauses_total", out["subclauses_total"], 2),
            ("syntax", cat["Syntax"], 1),
            ("legality", cat["Legality Rules"], 2),
            ("bounded", cat["Bounded (Run-Time) Errors"], 1),
            ("erroneous-with-dotted", cat["Erroneous Execution"], 2),
            ("intro", out["paragraphs_uncategorized"], 3),
            ("carrying-legality",
             out["subclauses_carrying_category"]["Legality Rules"], 1),
        ]
        for name, got, want in checks:
            if got != want:
                ok = False
            print("%s %-22s got %s want %s"
                  % ("ok " if got == want else "FAIL", name, got, want))
        titles = [s["title"] for s in out["subclauses"]]
        if titles != ["(clause intro)", "Task Units", "Task Execution"]:
            print("FAIL titles                 got %s" % titles)
            ok = False
        else:
            print("ok  titles")
    print("self-test:", "PASSED" if ok else "FAILED")
    return 0 if ok else 1


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("directory", nargs="?")
    ap.add_argument("-o", "--output")
    ap.add_argument("--compare", help="a previous census JSON; report the delta")
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()

    if args.self_test:
        return self_test()
    if not args.directory:
        sys.exit("ada_spec_census: a directory of RM-*.TXT files is required")
    if not os.path.isdir(args.directory):
        sys.exit("ada_spec_census: not a directory: %s" % args.directory)

    out = build(args.directory)
    text = json.dumps(out, indent=2, sort_keys=True) + "\n"

    if args.compare:
        with open(args.compare) as fh:
            old = json.load(fh)
        drift = 0
        for key in ("paragraphs_total", "subclauses_total", "clauses_total"):
            if old.get(key) != out[key]:
                print("%-28s %s -> %s" % (key, old.get(key), out[key]))
                drift += 1
        for c in CATEGORIES:
            a = old.get("paragraphs_by_category", {}).get(c)
            b = out["paragraphs_by_category"][c]
            if a != b:
                print("%-28s %s -> %s" % (c, a, b))
                drift += 1
        print("compare: %d differences" % drift)
        return 1 if drift else 0

    if args.output:
        with open(args.output, "w") as fh:
            fh.write(text)
        b = out["paragraphs_by_category"]
        print("ARM census: %d paragraphs in %d subclauses across %d clauses | "
              "Legality %d, Static %d, Dynamic %d, Bounded %d, Erroneous %d"
              % (out["paragraphs_total"], out["subclauses_total"],
                 out["clauses_total"], b["Legality Rules"],
                 b["Static Semantics"], b["Dynamic Semantics"],
                 b["Bounded (Run-Time) Errors"], b["Erroneous Execution"]))
    else:
        sys.stdout.write(text)
    return 0


if __name__ == "__main__":
    sys.exit(main())
