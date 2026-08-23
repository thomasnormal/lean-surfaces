#!/usr/bin/env python3
"""ada_suite_census.py — what is actually in the ACATS, measured.

Ada is the only language in the family whose conformance suite is OFFICIAL:
the ACATS is the corpus ISO/IEC 18009 conformity assessments are conducted
with, published by the ACAA.  `docs/ada-charter.md` prices a tier against it,
and pricing against a suite nobody counted would be the same mistake the C
tier's charter was written to stop making.

    python3 harness/ada_suite_census.py <unpacked-ACATS-dir> [-o out.json]
    python3 harness/ada_suite_census.py <dir> --compare docs/ada-suite-census.json
    python3 harness/ada_suite_census.py --self-test

WHAT A TEST IS.  The ACATS names files, not tests: a test may span several
files whose names share a seven-character prefix (User's Guide 4.3).  This
groups by that prefix.  Foundations (`F...`) are not tests and are counted
apart; so are the four `CZ` tests, which check the reporting code rather than
the language.  The grouping is VALIDATED against the User's Guide's own
table (4.1) — 4188 tests, 3996 core, 192 SNA, 70 foundations — and the
instrument reports the numbers so the agreement can be checked rather than
believed.

WHAT IS MEASURED PER TEST.  Class (the first character), legacy vs modern
naming (the seventh character is a letter vs a digit), core vs Specialized
Needs Annex, the clause under test, the files and their extensions, the
foundation it needs, its size, whether it carries the ACAA's per-file rights
grant, the B-test error markings, the Report-package protocol calls it makes,
the library units it `with`s, and which Ada features it uses.

HOW FEATURES ARE DETECTED, and the limit of it.  There is NO Ada frontend on
this host, so this is a LEXICAL census: comments, string literals and
character literals are removed by a small Ada scanner (`strip`), and the
remaining reserved words are counted.  Reserved words are unambiguous once
literals are gone, so the buckets built from them are exact.  Constructs that
are NOT a reserved word — representation clauses, aspect specifications,
generic instantiation — are deliberately NOT bucketed rather than
approximated: the charter's first milestone is a frontend census, and that is
where they get settled.  A lexical census that quietly guessed at them would
be the "silent wrong answer" this repository does not ship.

REFUSAL PATHS.  A missing directory refuses.  A directory with no test files
refuses.  A run that classifies ZERO tests refuses — an empty census is an
instrument fault, never a finding.  A file that cannot be decoded refuses by
name.

Python >= 3.9, stdlib only.  Deterministic: sorted output, byte-identical on
a double run.
"""

import argparse
import collections
import json
import os
import re
import sys

# Directories that hold no tests.  `support` carries the Report package, the
# ImpDef customization packages, the macro substituter and the foundations;
# `docs` is the User's Guide.
NON_TEST_DIRS = {"SUPPORT", "DOCS"}

# The classes, User's Guide 4.2.  B and L are the two that expect a REJECTION
# rather than a run, which is the verdict shape the family does not have yet.
CLASSES = {
    "A": "compiles, runs, reports PASSED (legacy only)",
    "B": "must be REJECTED at compile time, at marked lines",
    "C": "compiles, runs, reports PASSED or NOT-APPLICABLE",
    "D": "exact arithmetic on large literals; a capacity error also passes",
    "E": "runs and reports TENTATIVELY PASSED; graded by inspection",
    "L": "must fail to BIND; must not begin execution",
}

# Test-name prefixes that the User's Guide counts as `Other` rather than as
# tests: the CZ tests check the ACATS's own reporting code.
NOT_LANGUAGE = ("CZ",)

# `FCNDECL` begins with F but is a customization package (User's Guide
# 5.2.3), not a foundation.  Counting it as one is off by exactly the amount
# that stops this census reproducing the User's Guide's own table, which is
# how it was found.
NOT_FOUNDATIONS = {"FCNDECL"}

# ACATS extensions, User's Guide 4.3.1 and 4.3.2.
EXTENSIONS = {
    ".A": "Ada source, modern naming",
    ".AM": "Ada source carrying the main subprogram of a multi-file test",
    ".AU": "Ada source with characters outside 7-bit ASCII (UTF-8 with BOM)",
    ".ADA": "Ada source, legacy naming",
    ".DEP": "legacy test of implementation-dependent features",
    ".TST": "legacy test carrying macro symbols; must be expanded first",
    ".C": "C source, for a foreign-language-interface test",
    ".FTN": "Fortran source, for a foreign-language-interface test",
    ".CBL": "Cobol source, for a foreign-language-interface test",
}
ADA_EXTENSIONS = {".A", ".AM", ".AU", ".ADA", ".DEP", ".TST"}

# Ada 2012/2022 reserved words (ARM 2.9).  Case-insensitive.
RESERVED = """abort abs abstract accept access aliased all and array at begin
body case constant declare delay delta digits do else elsif end entry
exception exit for function generic goto if in interface is limited loop mod
new not null of or others out overriding package parallel pragma private
procedure protected raise range record rem renames requeue return reverse
select separate some subtype synchronized tagged task terminate then type
until use when while with xor""".split()

# Feature buckets, each a set of RESERVED WORDS — so each is exact once
# literals are stripped.  A bucket is "used" by a test when any of its words
# appears anywhere in the test's Ada files.
BUCKETS = collections.OrderedDict([
    ("tasking", ["task", "protected", "entry", "accept", "select", "requeue",
                 "delay", "abort", "terminate", "synchronized"]),
    ("generics", ["generic"]),
    ("tagged-types", ["tagged", "abstract", "interface", "overriding"]),
    ("access-types", ["access", "aliased"]),
    ("exceptions", ["exception", "raise"]),
    ("separate-compilation", ["separate", "limited", "private"]),
    ("real-types", ["digits", "delta"]),
    ("goto", ["goto"]),
    ("parallel", ["parallel"]),
])

# One bucket is NOT a reserved word and is worth the exception, because
# leaving it out would understate Ada's scale badly: a generic INSTANTIATION
# is `package P is new Q(...)` (also `procedure`/`function`), with no
# `generic` keyword anywhere.  A test can instantiate the whole predefined
# generic library and never write `generic`.  The shape is unambiguous —
# a DERIVED TYPE is `type T is new S`, which starts with `type` — so this one
# is measured by shape and named as such.  Everything else that is not a
# reserved word (representation clauses, aspect specifications) stays
# UNMEASURED rather than approximated; the frontend census settles those.
INSTANTIATION = re.compile(
    r"(?i)\b(?:package|procedure|function)\s+[A-Za-z]\w*(?:\.\w+)*\s*"
    r"(?:\([^;()]*\)\s*)?(?:return\s+[\w.]+\s*)?is\s+new\b")

# The B/L marking vocabulary, User's Guide 4.2.2 and 4.2.6.
MARKINGS = collections.OrderedDict([
    ("ERROR:", re.compile(r"--\s*ERROR:")),
    ("OPTIONAL ERROR:", re.compile(r"--\s*OPTIONAL\s+ERROR:?")),
    ("POSSIBLE ERROR:", re.compile(r"--\s*POSSIBLE\s+ERROR:")),
    ("OK", re.compile(r"--\s*OK\b")),
    ("ANX-C RQMT", re.compile(r"--\s*ANX-C\s+RQMT")),
])

# The Report package protocol, User's Guide 4.6 — the suite's ORACLE.
REPORT_CALLS = ["Test", "Failed", "Not_Applicable", "Special_Action",
                "Comment", "Result", "Ident_Int", "Ident_Char",
                "Ident_Wide_Char", "Ident_Bool", "Ident_Str", "Ident_Wide_Str",
                "Equal", "Legal_File_Name", "Time_Stamp"]
# Legacy tests write `USE REPORT;` and then call `TEST (...)` unqualified, so
# looking only for `Report.Test` finds a fraction of the suite and would make
# the oracle look far narrower than it is.  Measured on `C23001A.ADA`, which
# is the shape.
USE_REPORT = re.compile(r"(?i)\buse\b[^;]*\breport\b[^;]*;")

# `Ada`, `System` and `Interfaces` are the three roots of the predefined
# environment (ARM A.2); the rest are Ada-83 top-level names that legacy
# tests still `with` and that ARM Annex J keeps.  Anything else a test `with`s
# is either ACATS machinery or a unit the test itself declares.
PREDEFINED_ROOTS = {"ADA", "SYSTEM", "INTERFACES", "STANDARD"}
PREDEFINED_LEGACY = {
    "TEXT_IO", "SEQUENTIAL_IO", "DIRECT_IO", "IO_EXCEPTIONS", "CALENDAR",
    "MACHINE_CODE", "LOW_LEVEL_IO", "UNCHECKED_CONVERSION",
    "UNCHECKED_DEALLOCATION",
}
ACATS_SUPPORT = {"REPORT", "IMPDEF", "TCTOUCH", "SPPRT13", "FCNDECL",
                 "CHECK_FILE", "ENUMCHECK", "ENUMCHEK", "MACROSUB"}

# The ACAA's per-file rights grant.  Measured, never assumed: the family's
# law is per-file licenses, and a suite-wide claim read off one header would
# be exactly the c-testsuite trap `docs/c23-goal.md` §2 records.
#
# Two detectors, deliberately, and the difference between them is a finding.
#
# Keying on the HEADING alone misses files that carry the operative sentence
# under no heading; keying on the OPERATIVE SENTENCE is what decides the
# licence.  And the grantor is not one party: measured, the suite carries the
# same grant of unlimited rights from the U.S. Government (older tests, under
# named DoD contracts), from the ACAA, and from AdaCore (contributed tests).
# So the census matches the OPERATIVE VERB and reports WHO granted, by name,
# with an `other` bucket that is listed rather than swallowed — looking for
# any one grantor would have reported most of the suite unlicensed, which is
# the shape of a silently wrong answer.
GRANT_TITLE = "Grant of Unlimited Rights"
GRANT_OP = re.compile(r"(?i)((?:\S+\s+){0,10}?)(?:holds|obtained)\s+unlimited"
                      r"\s+rights\s+in\s+the\s+software")
GRANTORS = [("acaa", re.compile(r"(?i)ACAA|Conformity\s+Assessment\s+Authority")),
            ("us-government", re.compile(r"(?i)U\.S\.\s+Government|Government")),
            ("adacore", re.compile(r"(?i)AdaCore"))]
COMMENT_LEAD = re.compile(r"(?m)^\s*--\s?")

CONTEXT_CLAUSE = re.compile(
    r"(?im)^[ \t]*(?:limited[ \t]+)?(?:private[ \t]+)?with[ \t]+"
    r"([A-Za-z][\w.]*(?:[ \t]*,[ \t]*[A-Za-z][\w.]*)*)[ \t]*;")


def strip(src):
    """Remove Ada comments, string literals and character literals.

    Ada's `'` is both the character-literal bracket and the attribute prefix
    (`Integer'Last`), so a naive scanner eats the rest of the file at the
    first attribute.  The rule used here is the one the language actually
    has: `'x'` is a character literal only when the token before it cannot
    end a name — otherwise the tick is an attribute or a qualified
    expression.  `'"'` is the case that makes this worth doing right."""
    out, i, n = [], 0, len(src)
    prev = ""
    while i < n:
        c = src[i]
        if c == "-" and src.startswith("--", i):
            j = src.find("\n", i)
            i = n if j < 0 else j
            continue
        if c == '"':
            j = i + 1
            while j < n:
                if src[j] == '"':
                    if j + 1 < n and src[j + 1] == '"':
                        j += 2
                        continue
                    break
                if src[j] == "\n":
                    break
                j += 1
            out.append(" ")
            i = j + 1
            prev = " "
            continue
        if c == "'" and i + 2 < n and src[i + 2] == "'" and not (
                prev.isalnum() or prev in "_)"):
            out.append(" ")
            i += 3
            prev = " "
            continue
        out.append(c)
        if not c.isspace():
            prev = c
        i += 1
    return "".join(out)


def words(stripped):
    return collections.Counter(w.lower() for w in
                               re.findall(r"[A-Za-z_]\w*", stripped))


def read(path):
    try:
        with open(path, "rb") as fh:
            raw = fh.read()
    except OSError as exc:
        sys.exit("ada_suite_census: cannot read %s: %s" % (path, exc))
    for enc in ("utf-8-sig", "latin-1"):
        try:
            return raw.decode(enc)
        except UnicodeDecodeError:
            continue
    sys.exit("ada_suite_census: cannot decode %s" % path)


def collect(root):
    """Group files into tests, foundations and support, by the ACATS's own
    naming convention."""
    tests, foundations, support, docs = (collections.defaultdict(list),
                                         collections.defaultdict(list), [], [])
    for dirpath, _, filenames in os.walk(root):
        base = os.path.basename(dirpath).upper()
        for name in sorted(filenames):
            path = os.path.join(dirpath, name)
            if dirpath == root:
                support.append(path)
                continue
            if base == "DOCS":
                docs.append(path)
                continue
            stem, ext = os.path.splitext(name)
            key = stem[:7].upper()
            is_foundation = (key.startswith("F") and key not in NOT_FOUNDATIONS
                             and ext.upper() in ADA_EXTENSIONS)
            if base == "SUPPORT":
                # The foundations live beside the Report package; everything
                # else in `support` is machinery, not a test.
                (foundations[key] if is_foundation else support).append(path)
            elif is_foundation:
                foundations[key].append(path)
            else:
                tests[key].append(path)
    return tests, foundations, support, docs


def clause_of(name):
    """The clause under test, read off the name (User's Guide 4.3.2).

    Modern names encode it; legacy names encode an ACVC Implementer's Guide
    chapter that follows Ada 83's organization and, the User's Guide says in
    4.3.1, "sometimes will not correspond" to the current clause.  So legacy
    tests get their chapter reported as such and never as an ARM clause."""
    # ACATS names are 7 or 8 characters (User's Guide 4.3.1, 4.3.2) and a
    # real delivery has no shorter one -- but a MALFORMED delivery would
    # crash here with an IndexError, and a traceback is not a refusal.
    # Found by this instrument's own refusal-path fixture.
    if len(name) < 7:
        sys.exit("ada_suite_census: test name %r is shorter than the 7 "
                 "characters the ACATS naming convention requires (User's "
                 "Guide 4.3). This is not an ACATS delivery, or it is "
                 "damaged; guessing a class and clause from it would be "
                 "worse than refusing." % name)
    modern = name[6].isdigit()
    if not modern:
        return {"naming": "legacy", "aig_chapter": name[1], "clause": None,
                "annex": None}
    if name[1].upper() == "X":
        return {"naming": "modern", "aig_chapter": None, "clause": None,
                "annex": name[2].upper()}
    return {"naming": "modern", "aig_chapter": None,
            "clause": name[1].upper(), "annex": None}


def census_test(name, paths):
    ada = [p for p in paths if os.path.splitext(p)[1].upper() in ADA_EXTENSIONS]
    text, lines, titled = [], 0, 0
    grantors = collections.Counter()
    for p in sorted(ada):
        src = read(p)
        lines += src.count("\n")
        if GRANT_TITLE in src:
            titled += 1
        flat = " ".join(COMMENT_LEAD.sub("", src).split())
        m = GRANT_OP.search(flat)
        if m:
            who = m.group(1)
            grantors[next((n for n, r in GRANTORS if r.search(who)),
                          "other:" + who.strip()[-40:])] += 1
        text.append(src)
    granted = sum(grantors.values())
    joined = "".join(text)
    bare = strip(joined)
    wc = words(bare)
    marks = {k: len(r.findall(joined)) for k, r in MARKINGS.items()}
    withs = set()
    for m in CONTEXT_CLAUSE.finditer(bare):
        for unit in m.group(1).split(","):
            unit = unit.strip()
            # `with private;` and `with null record;` are private extension
            # declarations, not context clauses.  Ada is case-insensitive, so
            # the names are folded before counting or `REPORT` and `Report`
            # would be two units.
            if unit.lower() in RESERVED:
                continue
            withs.add(unit.upper())
    used = bool(USE_REPORT.search(bare))
    calls = sorted({c for c in REPORT_CALLS
                    if re.search(r"(?i)\bReport\s*\.\s*%s\b" % c, bare)
                    or (used and re.search(r"(?i)\b%s\s*[(;]" % c, bare))})
    info = clause_of(name)
    row = {
        "test": name,
        "class": name[0].upper(),
        "files": sorted(os.path.basename(p) for p in paths),
        "extensions": sorted({os.path.splitext(p)[1].upper() for p in paths}),
        "ada_files": len(ada),
        "lines": lines,
        "rights_grant_files": granted,
        "rights_grantors": dict(sorted(grantors.items())),
        "rights_grant_titled_files": titled,
        "foundation": (name[1:5].upper() if info["naming"] == "modern"
                       and name[4].isalpha() else None),
        "markings": marks,
        "report_calls": calls,
        "withs": sorted(withs),
        "uses_report": used or bool(calls),
        "reserved": sorted(w for w in RESERVED if wc.get(w)),
        "instantiation_sites": len(INSTANTIATION.findall(bare)),
        "buckets": sorted(
            [b for b, ws in BUCKETS.items() if any(wc.get(w) for w in ws)]
            + (["instantiation"] if INSTANTIATION.search(bare) else [])),
    }
    row.update(info)
    row["sna"] = bool(info["annex"] and info["annex"] in "CDEFGH")
    row["language_test"] = not name.startswith(NOT_LANGUAGE)
    return row


def ladder(rows, steps=10):
    """The greedy reach ladder: at each step add the ONE feature bucket that
    unblocks the most still-blocked tests.  Mirrors `harness/c_suite_census.py`
    so the two tiers' reach numbers are comparable.

    This is reach of the FEATURE SET, i.e. what a tier must cover to accept
    the test at all.  It is not a claim that any semantics would run it:
    there is no Ada semantics.  The ladder prices what to build first."""
    have, out = set(), []
    blocked = [set(r["buckets"]) for r in rows]
    candidates = list(BUCKETS) + ["instantiation"]
    out.append({"step": 0, "added": None,
                "cleared": sum(1 for b in blocked if not b - have)})
    for step in range(1, steps + 1):
        best, gain = None, -1
        for cand in candidates:
            if cand in have:
                continue
            g = sum(1 for b in blocked if b - have and not b - (have | {cand}))
            if g > gain or (g == gain and best is not None and cand < best):
                best, gain = cand, g
        if best is None:
            break
        have.add(best)
        out.append({"step": step, "added": best,
                    "cleared": sum(1 for b in blocked if not b - have)})
    return out


def summarize(rows, foundations, support, docs):
    lang = [r for r in rows if r["language_test"]]
    core = [r for r in lang if not r["sna"]]
    sna = [r for r in lang if r["sna"]]
    by_class = collections.Counter(r["class"] for r in lang)
    by_naming = collections.Counter(r["naming"] for r in lang)
    marks = collections.Counter()
    for r in rows:
        for k, v in r["markings"].items():
            marks[k] += v
    withs = collections.Counter()
    for r in rows:
        for u in r["withs"]:
            withs[u] += 1
    buckets = collections.Counter()
    for r in lang:
        for b in r["buckets"]:
            buckets[b] += 1
    calls = collections.Counter()
    for r in rows:
        for c in r["report_calls"]:
            calls[c] += 1
    b_tests = [r for r in lang if r["class"] == "B"]
    sequential = [r for r in lang if "tasking" not in r["buckets"]]

    def kind(unit):
        if unit in PREDEFINED_LEGACY or unit.split(".")[0] in PREDEFINED_ROOTS:
            return "predefined"
        if unit in ACATS_SUPPORT:
            return "acats-support"
        return "test-local"

    grantors = collections.Counter()
    for r in rows:
        grantors.update(r["rights_grantors"])
    with_kinds = collections.Counter(kind(u) for u in withs)
    predefined = {u: n for u, n in withs.items() if kind(u) == "predefined"}
    test_files = sum(len(r["files"]) for r in rows)
    foundation_files = sum(len(v) for v in foundations.values())
    return {
        "tests_language": len(lang),
        "tests_core": len(core),
        "tests_sna": len(sna),
        "tests_non_language": len(rows) - len(lang),
        "foundation_units": len(foundations),
        "foundation_files": foundation_files,
        "support_files": len(support),
        "doc_files": len(docs),
        "test_files": test_files,
        "files_total": test_files + foundation_files + len(support) + len(docs),
        "lines_total": sum(r["lines"] for r in rows),
        "by_class": dict(sorted(by_class.items())),
        "by_naming": dict(sorted(by_naming.items())),
        "rights_grant_files": sum(r["rights_grant_files"] for r in rows),
        "rights_grantors": dict(sorted(grantors.items())),
        "rights_grant_titled_files": sum(r["rights_grant_titled_files"]
                                         for r in rows),
        "ada_files_without_grant": sum(r["ada_files"] - r["rights_grant_files"]
                                       for r in rows),
        "ada_files": sum(r["ada_files"] for r in rows),
        "markings": dict(marks),
        "b_tests_with_error_marks": sum(1 for r in b_tests
                                        if r["markings"]["ERROR:"]),
        "error_marks_in_b_tests": sum(r["markings"]["ERROR:"] for r in b_tests),
        "report_calls": dict(sorted(calls.items())),
        "tests_calling_report_test": calls.get("Test", 0),
        "withs_distinct": len(withs),
        "withs_by_kind": dict(sorted(with_kinds.items())),
        "withs_predefined": dict(sorted(predefined.items(),
                                        key=lambda kv: (-kv[1], kv[0]))),
        "tests_withing_no_predefined": sum(
            1 for r in lang
            if not any(kind(u) == "predefined" for u in r["withs"])),
        "tests_using_report": sum(1 for r in lang if r["uses_report"]),
        "buckets": dict(sorted(buckets.items())),
        "tests_no_bucket": sum(1 for r in lang if not r["buckets"]),
        "sequential_tests": len(sequential),
        "sequential_core_tests": sum(1 for r in sequential if not r["sna"]),
    }


SELF_TEST_FILES = {
    "c3/C340001.A": """\
-- C340001.A
--                             Grant of Unlimited Rights
--     The Ada Conformity Assessment Authority (ACAA) holds unlimited
--     rights in the software and documentation contained herein.
with Report;
with Ada.Text_IO, Ada.Finalization;
procedure C340001 is
   type Derived is new Integer;           -- NOT an instantiation
   package Sorter is new Generic_Sort (Derived);   -- an instantiation
   S : constant String := "-- ERROR: not a marking, it is in a literal";
   Q : constant Character := '"';         -- the tick trap
   N : constant Integer := Integer'Last;  -- an attribute, not a literal
begin
   Report.Test ("C340001", "A description");
   if Report.Ident_Int (1) /= 1 then
      Report.Failed ("Reason");
   end if;
   Report.Result;
end C340001;
""",
    # The grant WITHOUT its heading — the shape 14 real files have, and the
    # reason the census carries two detectors.
    "b3/B340001.A": """\
-- B340001.A
--     The Ada Conformity Assessment Authority (ACAA) holds unlimited
--     rights in the software and documentation contained herein.
procedure B340001 is
   task T;                                     -- OK
   X : Integer := "oops";                      -- ERROR: type mismatch
   Y : Integer := 1;                           -- OPTIONAL ERROR:
begin
   null;                                       -- POSSIBLE ERROR: something
end B340001;
""",
    # The legacy style: `USE REPORT;` and then UNQUALIFIED calls.  Looking
    # only for `Report.Test` finds a fraction of the suite.
    "c2/C23001A.ADA": """\
-- C23001A.ADA
--                             Grant of Unlimited Rights
--     Under contracts F33600-87-D-0337, the U.S. Government obtained
--     unlimited rights in the software and documentation contained herein.
WITH REPORT;
PROCEDURE C23001A IS
        USE REPORT;
BEGIN
        TEST ("C23001A", "LEGACY STYLE");
        RESULT;
END C23001A;
""",
    "support/F340A00.A": "-- F340A00.A\npackage F340A00 is\nend F340A00;\n",
    "support/FCNDECL.ADA": "package FCNDECL is\nend FCNDECL;\n",
    "support/REPORT.A": "package Report is\nend Report;\n",
    "support/VERSION.A": ('package Version is\n   ACATS_Version : constant '
                          'String := "4.2 ";\nend Version;\n'),
    # The delivery's own file list. The census REFUSES without one (the
    # 2026-08-23 audit's absence row), so the fixture carries it -- and
    # listing every basename keeps `manifest_check` reporting no MISSING
    # file, which is the state a real delivery is in.
    "support/ACATS42.LST": ("C340001.A\nB340001.A\nC23001A.ADA\n"
                            "F340A00.A\nFCNDECL.ADA\nREPORT.A\n"
                            "VERSION.A\nACATS42.LST\nUG-1.HTM\n"),
    "docs/UG-1.HTM": "<html></html>\n",
}


def self_test():
    """The shapes that would silently produce a wrong answer are the ones the
    fixture is built from: a marking inside a STRING LITERAL, a `'"'`
    character literal, an attribute tick, a legacy ALL-CAPS test, a
    foundation, and the support and docs directories."""
    import tempfile
    ok = True
    with tempfile.TemporaryDirectory() as d:
        for rel, body in SELF_TEST_FILES.items():
            path = os.path.join(d, rel)
            os.makedirs(os.path.dirname(path), exist_ok=True)
            with open(path, "w") as fh:
                fh.write(body)
        out = build(d)
        s = out["summary"]
        rows = {r["test"]: r for r in out["tests"]}
        checks = [
            ("acats_version", out["acats_version"], "4.2"),
            ("language_version", out["language_version"], "Ada2012"),
            ("tests", s["tests_language"], 3),
            ("foundation_units", s["foundation_units"], 1),
            ("support_files", s["support_files"], 4),
            ("files_total", s["files_total"], len(SELF_TEST_FILES)),
            ("doc_files", s["doc_files"], 1),
            ("legacy", s["by_naming"].get("legacy"), 1),
            ("modern", s["by_naming"].get("modern"), 2),
            ("rights-grant-files", s["rights_grant_files"], 3),
            ("rights-grantors", s["rights_grantors"],
             {"acaa": 2, "us-government": 1}),
            ("rights-grant-titled", s["rights_grant_titled_files"], 2),
            ("ada-files-without-grant", s["ada_files_without_grant"], 0),
            # the marking in C340001 is inside a string literal and the
            # count is over RAW text, so it is seen there; the B test's four
            # markings are the ones a grader acts on.
            ("B ERROR: marks", rows["B340001"]["markings"]["ERROR:"], 1),
            ("B OPTIONAL", rows["B340001"]["markings"]["OPTIONAL ERROR:"], 1),
            ("B POSSIBLE", rows["B340001"]["markings"]["POSSIBLE ERROR:"], 1),
            ("B OK", rows["B340001"]["markings"]["OK"], 1),
            ("B tasking", "tasking" in rows["B340001"]["buckets"], True),
            # the tick trap: `'"'` must not swallow the file, so the withs
            # and the Report calls after it are still found.
            ("C withs", rows["C340001"]["withs"],
             ["ADA.FINALIZATION", "ADA.TEXT_IO", "REPORT"]),
            ("C report calls", rows["C340001"]["report_calls"],
             ["Failed", "Ident_Int", "Result", "Test"]),
            # `type Derived is new Integer` must NOT count as an
            # instantiation, and `package Sorter is new ...` must.
            ("C buckets", rows["C340001"]["buckets"], ["instantiation"]),
            ("C instantiations", rows["C340001"]["instantiation_sites"], 1),
            ("legacy report", rows["C23001A"]["report_calls"],
             ["Result", "Test"]),
            ("legacy chapter", rows["C23001A"]["aig_chapter"], "2"),
            ("modern clause", rows["C340001"]["clause"], "3"),
        ]
        for name, got, want in checks:
            if got != want:
                ok = False
            print("%s %-22s got %r want %r"
                  % ("ok " if got == want else "FAIL", name, got, want))
        # `strip` is the piece everything else rests on, so it is checked
        # directly too.
        cases = [
            ("X : Character := '\"'; Y := 1;", '"'),
            ("N := Integer'Last; -- comment\nM := 2;", "comment"),
            ('S := "a -- b"; T := 3;', "--"),
        ]
        for src, absent in cases:
            got = strip(src)
            if absent in got or not got.strip().endswith(";"):
                print("FAIL strip                 %r -> %r" % (src, got))
                ok = False
            else:
                print("ok  strip %-14r" % src[:14])
    print("self-test:", "PASSED" if ok else "FAILED")
    return 0 if ok else 1


def manifest_check(root):
    """The delivery ships its own file list (`support/ACATS42.LST`).  An
    incomplete unpack would shrink every number in this census silently, so
    when the list is present the census is checked against it and a MISSING
    file refuses.  Files on disk that the list does not name are reported,
    not refused — the delivery carries one (`DIRS.BAT`, a directory-creation
    script), and reporting it is how that was found."""
    listed = None
    for dirpath, _, filenames in os.walk(root):
        for name in filenames:
            if re.fullmatch(r"ACATS\d*\.LST", name, re.IGNORECASE):
                with open(os.path.join(dirpath, name), encoding="latin-1") as fh:
                    listed = {l.strip().upper() for l in fh if l.strip()}
                break
    if listed is None:
        sys.exit("ada_suite_census: no ACATS*.LST manifest under %s. It is "
                 "the delivery's own file list and the only way to know the "
                 "unpack is COMPLETE; without it an incomplete corpus would "
                 "shrink every number here silently, which is the failure "
                 "this check exists to prevent." % root)
    have = {n.upper() for _, _, fs in os.walk(root) for n in fs}
    missing = sorted(listed - have)
    if missing:
        sys.exit("ada_suite_census: %d file(s) the delivery's own list names "
                 "are not on disk, first %s — this census would understate "
                 "every count, which is a fault and not a finding"
                 % (len(missing), missing[0]))
    return {"listed": len(listed), "on_disk": len(have),
            "unlisted": sorted(have - listed)}


# Per-test detail the committed census does NOT carry, so the artifact stays
# the size of its siblings in `docs/`.  Three trims, each losing nothing a
# reader of the charter needs:
#
#   * `reserved` — the raw reserved-word list per test.  Pretty-printed one
#     word per line it is the single largest thing in the file, and `buckets`
#     already summarizes every decision-relevant fact in it.
#   * zero MARKINGS rows — most tests are class C and carry none, so five
#     lines of zeros each is 13k lines of nothing.
#   * TEST-LOCAL `with`s — 1764 of the 1907 distinct units are packages a
#     test declares for itself.  The library SURFACE, which is what §3.5 of
#     the charter is about, is the predefined and ACATS-support units.
#   * the per-test RIGHTS-GRANT fields — licence-audit detail whose totals and
#     grantor histogram the summary carries in full, and whose per-file check
#     is the instrument's job rather than a reader's.
#
# `--full` keeps everything.  The summary is computed BEFORE the trim, so no
# published number depends on which mode was used.
VERBOSE_FIELDS = ("reserved", "rights_grant_files", "rights_grantors",
                  "rights_grant_titled_files")


# Which Ada edition an ACATS baseline tests.  Recorded from the ACAA's own
# distribution page and User's Guide §1; the SUITE VERSION itself is read out
# of the delivery (`support/version.a` carries `ACATS_Version`) rather than
# inferred from a directory name, so pointing this instrument at another
# baseline reports that baseline rather than a lie about this one.
SUITE_EDITION = {"1": "Ada83", "2": "Ada95", "3": "Ada2005", "4": "Ada2012"}
VERSION_CONST = re.compile(r'(?i)ACATS_Version\s*:\s*constant\s+String\s*:=\s*"'
                           r'\s*([0-9]+(?:\.[0-9]+)?)')


def suite_version(root):
    """Read the suite's own version constant.  Returns (version, edition).

    REFUSES rather than recording `null`.  The 2026-08-23 audit found this
    returning `(None, None)` for a missing or unparseable `VERSION.A`, which
    was then written out verbatim as `"acats_version": null,
    "language_version": null` — an ABSENCE serialized as a measurement.  The
    edition is what tells a reader which Ada this census is about, so a
    census that cannot determine it has not measured the thing it names.
    """
    for dirpath, _, filenames in os.walk(root):
        for name in filenames:
            if name.upper() == "VERSION.A":
                path = os.path.join(dirpath, name)
                m = VERSION_CONST.search(read(path))
                if not m:
                    sys.exit("ada_suite_census: %s carries no readable "
                             "`ACATS_Version` constant. The suite version is "
                             "what fixes which Ada edition this census is "
                             "about; recording it as null would serialize an "
                             "absence as a measurement." % path)
                major = m.group(1).split(".")[0]
                edition = SUITE_EDITION.get(major)
                if edition is None:
                    sys.exit("ada_suite_census: ACATS major version %r is not "
                             "in SUITE_EDITION %r — this delivery is a "
                             "baseline this instrument has never seen, and "
                             "guessing its Ada edition would be worse than "
                             "refusing." % (major, sorted(SUITE_EDITION)))
                return m.group(1), edition
    sys.exit("ada_suite_census: no VERSION.A anywhere under %s. Every ACATS "
             "delivery ships one (support/version.a); without it the edition "
             "is unknown and a census that cannot say which Ada it measured "
             "is not a census." % root)


def build(root, full=False):
    manifest = manifest_check(root)
    tests, foundations, support, docs = collect(root)
    if not tests:
        sys.exit("ada_suite_census: no test files under %s — is this an "
                 "unpacked ACATS delivery?" % root)
    rows = [census_test(name, paths) for name, paths in sorted(tests.items())]
    if not rows:
        sys.exit("ada_suite_census: zero tests classified — instrument fault")
    lang = [r for r in rows if r["language_test"]]
    version, edition = suite_version(root)
    summary = summarize(rows, foundations, support, docs)
    if not full:
        for r in rows:
            for field in VERBOSE_FIELDS:
                r.pop(field, None)
            r["markings"] = {k: v for k, v in r["markings"].items() if v}
            r["withs"] = [u for u in r["withs"]
                          if u in PREDEFINED_LEGACY or u in ACATS_SUPPORT
                          or u.split(".")[0] in PREDEFINED_ROOTS]
    return {
        "instrument": "harness/ada_suite_census.py",
        # `docs/family-architecture.md` §5.4 requires an instrument to stamp
        # the frontend FAMILY, because the frontend is an INPUT to the result
        # and not decoration.  This one has no frontend, and saying so is the
        # honest stamp: every feature number below is lexical, and the
        # milestone that builds a real frontend is what replaces them.
        "frontend": "none — lexical scanner in this file; no Ada parser",
        "language": "Ada",
        "acats_version": version,
        "language_version": edition,
        "verbose_fields_included": full,
        "root": os.path.basename(os.path.abspath(root)),
        "manifest": manifest,
        "classes": CLASSES,
        "extensions": EXTENSIONS,
        "buckets": dict(list(BUCKETS.items())
                        + [("instantiation", ["<shape: `package|procedure|"
                                              "function <name> is new`>"])]),
        "summary": summary,
        "reach_ladder": ladder(lang),
        "reach_ladder_core": ladder([r for r in lang if not r["sna"]]),
        "tests": rows,
    }


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("directory", nargs="?")
    ap.add_argument("-o", "--output")
    ap.add_argument("--compare", help="a previous census JSON; report the delta")
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--full", action="store_true",
                    help="include the per-test reserved-word lists; the "
                         "committed census omits them (see VERBOSE_FIELDS)")
    args = ap.parse_args()

    if args.self_test:
        return self_test()
    if not args.directory:
        sys.exit("ada_suite_census: an unpacked ACATS directory is required")
    if not os.path.isdir(args.directory):
        sys.exit("ada_suite_census: not a directory: %s" % args.directory)

    out = build(args.directory, full=args.full)
    text = json.dumps(out, indent=2, sort_keys=True) + "\n"
    if args.compare:
        with open(args.compare) as fh:
            old = json.load(fh)["summary"]
        drift = 0
        for key, new in sorted(out["summary"].items()):
            if isinstance(new, dict):
                continue
            if old.get(key) != new:
                print("%-28s %s -> %s" % (key, old.get(key), new))
                drift += 1
        print("compare: %d differences" % drift)
        return 1 if drift else 0
    if args.output:
        with open(args.output, "w") as fh:
            fh.write(text)
        s = out["summary"]
        print("ACATS census: %d language tests (%d core, %d SNA), %d "
              "foundations in %d files, %d files total | classes %s | "
              "sequential %d"
              % (s["tests_language"], s["tests_core"], s["tests_sna"],
                 s["foundation_units"], s["foundation_files"],
                 s["files_total"], s["by_class"], s["sequential_tests"]))
    else:
        sys.stdout.write(text)
    return 0


if __name__ == "__main__":
    sys.exit(main())
