#!/usr/bin/env python3
"""c_citation_check.py — resolve the C tier's ISO citations against the drafts.

docs/family-architecture.md §5.5: clause citations must be CHECKED DATA, not
prose. This instrument makes them so. It reads the public working drafts, builds
each edition's clause table, extracts every citation in the C tier, resolves it
in the edition it claims, and reports what that clause is actually TITLED there.

WHY IT EXISTS. C23 renumbered 6.5, 6.8 and 5.1.2 wholesale (see
harness/c_clause_delta.py: 612 of 933 matched clauses moved), so a C17-era number
carried into a C23 document is plausible, silent and wrong. Three such citations
were found by hand; this instrument replaces the hand.

THE CITATION CONVENTION it implements (the C lane's, docs/c23-spec-mirror.md
§1.1a) — three exclusions, without which correct documentation reports as drift:

  1. An UNTAGGED `§` inside LeanModels/C/C23/ means C23. Resolve it there; it is
     not ambiguous and must not be flagged as such.
  2. A SUPERSEDED citation carries its edition tag immediately before the `§`
     ("C17 §6.5.5"). That is deliberate documentation of an older edition's
     number — resolve against the tagged edition, never against the default.
  3. A `§` on a line containing a `docs/*.md` token is an INTERNAL document
     reference, not an ISO citation. Skip it.

  4. A FOURTH exclusion, found by running this instrument and reported back to
     the C lane: inside a `.md` file, an UNTAGGED `§` is an internal section
     reference, not an ISO citation. These documents number their own sections
     §1..§7, which collides head-on with the standard's clauses 5, 6 and 7 —
     "the memo's §5.4", "(§5.2)", "§5.4's square" all resolved as ISO clauses
     and produced four MISSING rows that were pure noise. Rules 1-3 leave this
     case undefined; a `.lean` file has no section structure, so untagged is
     unambiguous there, but a `.md` file needs the tag. Untagged `.md`
     citations are counted and reported as `unclassified` rather than silently
     dropped, because the count is the size of the convention's blind spot.

VERDICTS, per citation:
  ok         the clause exists in the claimed edition; its title is reported
  MISSING    the number does not exist in the claimed edition — a hard error
  AMBIGUOUS  untagged, in a version-NEUTRAL location, and the number resolves to
             different titles in C17 and C23 — the renumbering hazard, exactly

Exit non-zero if any MISSING or AMBIGUOUS row is found. `ok` rows still need a
human or a clause manifest to confirm the citation says what the author meant:
this instrument proves the number RESOLVES, never that it is the right number.

    python3 harness/c_citation_check.py --c17 <n2310.txt> --c23 <n3220.txt>

The drafts are NOT in this repository and never will be — no ISO text is
vendored. Absent them the instrument refuses loudly rather than skipping.
"""
import argparse
import json
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent

# Reuse the clause-table parser that harness/c_clause_delta.py validates.
sys.path.insert(0, str(REPO / "harness"))
try:
    from c_clause_delta import body_clauses, load
except ImportError:  # pragma: no cover
    sys.exit("c_citation_check: harness/c_clause_delta.py not importable")

# "C17 §6.5.5" / "C23 §6.3.1.3" / "§6.5.5"; the tag must be IMMEDIATELY before.
CITE = re.compile(r"(?:(C\d{2})\s+)?§\s?(\d+(?:\.\d+)+|J\.\d+(?:\.\d+)*)")
DOC_TOKEN = re.compile(r"docs/[\w.-]+\.md")
VERSION_DIR = re.compile(r"LeanModels/C/(C\d{2})/")

# The C tier's own surfaces. Version-neutral unless a path says otherwise.
SCAN = ["LeanModels/C", "docs/c-semantics-design.md", "docs/c-tier-charter.md",
        "docs/c23-goal.md", "docs/c-profile.md", "docs/c-envelope-schema.md",
        "docs/c-tier-architecture.md"]

# An ISO clause citation starts at clause 5 (environment), 6 (language),
# 7 (library) or annex J. Lower numbers in these documents are section
# self-references (§2.3, §4.1), which is a house convention, not a citation.
ISO_HEADS = ("5", "6", "7", "J")


def files_to_scan():
    out = []
    for s in SCAN:
        p = REPO / s
        if p.is_dir():
            out.extend(sorted(q for q in p.rglob("*") if q.suffix in (".lean", ".md")))
        elif p.is_file():
            out.append(p)
    return out


def default_edition(path, fallback):
    m = VERSION_DIR.search(str(path).replace("\\", "/"))
    return m.group(1) if m else fallback


def scan(tables, fallback):
    rows, bad, unclassified = [], 0, []
    for f in files_to_scan():
        rel = f.relative_to(REPO).as_posix()
        is_md = f.suffix == ".md"
        for n, line in enumerate(f.read_text(encoding="utf-8", errors="replace")
                                 .splitlines(), 1):
            if DOC_TOKEN.search(line):
                continue                                  # exclusion 3
            for tag, num in CITE.findall(line):
                if not num.split(".")[0] in ISO_HEADS:
                    continue
                if is_md and not tag:                     # exclusion 4
                    unclassified.append({"file": rel, "line": n, "cited": num})
                    continue
                ed = tag or default_edition(f, fallback)  # exclusions 1 and 2
                tagged = bool(tag)
                row = {"file": rel, "line": n, "cited": num, "edition": ed,
                       "tagged": tagged,
                       "neutral_default": (not tagged
                                           and not VERSION_DIR.search(rel)),
                       "title": None, "title_other": None, "verdict": "ok"}
                tbl = tables.get(ed)
                if tbl is None:
                    row["verdict"] = "MISSING"
                    row["why"] = f"no draft supplied for edition {ed}"
                elif num not in tbl:
                    row["verdict"] = "MISSING"
                    row["why"] = f"clause {num} does not exist in {ed}"
                else:
                    row["title"] = tbl[num][1]
                    other = "C17" if ed == "C23" else "C23"
                    if other in tables and num in tables[other]:
                        row["title_other"] = tables[other][num][1]
                        if (row["neutral_default"]
                                and row["title_other"].lower() != row["title"].lower()):
                            row["verdict"] = "AMBIGUOUS"
                            row["why"] = (f"untagged in a version-neutral file; "
                                          f"{ed}={row['title']!r} but "
                                          f"{other}={row['title_other']!r}")
                if row["verdict"] != "ok":
                    bad += 1
                rows.append(row)
    return rows, bad, unclassified


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--c17", help="path to the C17 working-draft text (N2310)")
    ap.add_argument("--c23", required=True,
                    help="path to the C23 working-draft text (N3220)")
    ap.add_argument("--default-edition", default="C23",
                    help="edition for an untagged citation outside a version dir")
    ap.add_argument("-o", "--out")
    a = ap.parse_args()

    tables = {}
    for ed, path in (("C17", a.c17), ("C23", a.c23)):
        if not path:
            continue
        if not Path(path).is_file():
            sys.exit(f"c_citation_check: no such draft: {path}")
        t = body_clauses(load(path))
        if len(t) < 200:
            sys.exit(f"c_citation_check: {ed} yielded only {len(t)} clauses — refusing")
        tables[ed] = t
    if "C23" not in tables:
        sys.exit("c_citation_check: the C23 draft is required")

    rows, bad, unclassified = scan(tables, a.default_edition)
    if not rows:
        sys.exit("c_citation_check: ZERO citations found — instrument fault, not a finding")

    out = {"instrument": "harness/c_citation_check.py",
           "clauses_loaded": {k: len(v) for k, v in tables.items()},
           "citations": len(rows), "problems": bad,
           "unclassified_untagged_md": unclassified,
           "rows": sorted(rows, key=lambda r: (r["file"], r["line"], r["cited"]))}
    if a.out:
        Path(a.out).write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")

    print(f"c_citation_check: {len(rows)} ISO citations, {bad} problem(s); "
          f"{len(unclassified)} untagged .md refs unclassified (exclusion 4)")
    for r in out["rows"]:
        mark = " " if r["verdict"] == "ok" else "!"
        tag = f"{r['edition']}{'' if r['tagged'] else '*'}"
        print(f" {mark} {r['file']}:{r['line']}  {tag:6s} §{r['cited']:<10s} "
              f"{r['verdict']:<9s} {r['title'] or r.get('why', '')}")
    print("   (* = edition implied by location, not tagged in the text)")
    if unclassified:
        print("   unclassified (untagged § in a .md file — tag it to have it checked):")
        for u in unclassified:
            print(f"     - {u['file']}:{u['line']} §{u['cited']}")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
