#!/usr/bin/env python3
"""ada_construct_census.py — what Ada constructs does the corpus actually use?

`docs/ada-envelope-schema.md` §3 deliberately contains NO node table, and
says why: `docs/ada-charter.md` §3.1 measured **316 concrete node kinds** in
libadalang's grammar against C's 45, and choosing a subset of 316 before any
parser had run on any Ada would be an unverified claim about a language.
**This is the instrument that replaces the rule with a table.** The schema's
vocabulary is GENERATED from this output, and a check asserts the two are the
same SET — neither subset nor superset — so "what the ingester accepts" and
"what the corpus contains" cannot silently drift apart.

    python3 harness/ada_construct_census.py <dir-or-file> [-o out.json]
    python3 harness/ada_construct_census.py <dir> --compare docs/ada-construct-census.json
    python3 harness/ada_construct_census.py <dir> --limit 300
    python3 harness/ada_construct_census.py --self-test

IT NEEDS libadalang, and refuses loudly without it — see
`harness/ada_toolchain_census.py` for the acquisition path and the exact
environment (the Python bindings are ctypes over a SHARED library, so both
`PYTHONPATH` and `DYLD_LIBRARY_PATH`/`LD_LIBRARY_PATH` matter).

WHAT IS MEASURED, and by what rule.

* A SOURCE is any file with an ACATS Ada extension (`.a .am .au .ada .dep`).
  `.tst` files are EXCLUDED and counted: they carry macro symbols and are not
  Ada until expanded (ACATS User's Guide 4.3.1), so parsing one measures a
  macro processor's absence rather than a corpus's vocabulary.
* CRLF is converted before parsing, and the conversion is recorded per file.
  The ZIP delivery ships CRLF; the ACAA's own tools die on it (backlog §L69).
* A file with PARSE DIAGNOSTICS is reported as `diagnostics`, never as a
  small program, and the count is SPLIT BY TEST CLASS — a class B or L test
  contains deliberate illegalities, so the frontend rejecting one is the
  corpus working as designed, while a class C test that will not parse is a
  finding. Pooling them would make the number unreadable — libadalang returns a partial tree alongside its errors, and
  counting that would be a wrong answer rather than a smaller one. This is
  the C instrument's clang lesson, transferred: `docs/c-tier-charter.md` §1.1
  records it as a defect found only by executing the broken-input fixture.
* COMPILATION UNITS are read from the tree, never from the path — the file
  name is systematically not a unit name in ACATS
  (`docs/ada-envelope-schema.md` §0.2).

REFUSAL PATHS.  A missing path refuses.  A directory with no Ada sources
refuses.  A run that finds ZERO node kinds refuses — an empty census is an
instrument fault, never a finding.

Python >= 3.9 plus libadalang; otherwise stdlib only.  Deterministic: sorted
output, byte-identical on a double run.
"""

import argparse
import collections
import json
import os
import sys
import tempfile

# ACATS extensions that ARE Ada (User's Guide 4.3.1, 4.3.2).  `.tst` is not:
# it carries macro symbols and must be expanded first.
ADA_EXTS = {".a", ".am", ".au", ".ada", ".dep"}
MACRO_EXTS = {".tst"}

ACQUIRE = ("ada_construct_census: libadalang is not importable.  It is the "
           "tier's frontend and there is no fallback for this instrument.  "
           "Run `python3 harness/ada_toolchain_census.py` for the acquisition "
           "path; note the Python bindings are ctypes over a SHARED library, "
           "so PYTHONPATH must contain the bindings' PARENT directory and "
           "DYLD_LIBRARY_PATH (or LD_LIBRARY_PATH) must contain every built "
           "dependency's directory, not only libadalang's own.")


def load_lal():
    try:
        import libadalang as lal
    except Exception as exc:                      # noqa: BLE001 — reported
        sys.exit("%s\n  underlying error: %s" % (ACQUIRE, exc))
    return lal


def sources(root, limit=None):
    """Ada sources, sorted, plus the macro files set aside and counted."""
    if os.path.isfile(root):
        return [root], []
    found, macro = [], []
    for dirpath, _, filenames in os.walk(root):
        for name in sorted(filenames):
            ext = os.path.splitext(name)[1].lower()
            path = os.path.join(dirpath, name)
            if ext in ADA_EXTS:
                found.append(path)
            elif ext in MACRO_EXTS:
                macro.append(path)
    found.sort()
    macro.sort()
    if limit is not None:
        found = found[:limit]
    return found, macro


def normalized(path, tmpdir):
    """A copy with CRLF stripped, plus whether it needed stripping."""
    with open(path, "rb") as fh:
        data = fh.read()
    crlf = b"\r\n" in data
    out = os.path.join(tmpdir, os.path.basename(path))
    with open(out, "wb") as fh:
        fh.write(data.replace(b"\r\n", b"\n"))
    return out, crlf


def unit_names(root):
    """Compilation-unit names, read from the TREE.  In ACATS the file name is
    systematically not a unit name (the eighth character is a compilation
    ORDER digit), so deriving them from the path is the §L67 mistake.

    THE ROOT SHAPE DIFFERS BY FILE and iterating `root.children` is wrong.
    Measured: a source with ONE compilation unit parses to a root whose own
    kind is `CompilationUnit` (whose three children are the prelude list, the
    `LibraryItem` and a pragma list); a source with SEVERAL parses to a
    `CompilationUnitList`.  Walking the children of the first shape yields
    three non-units and no name — a silently wrong answer, caught by the
    self-test.  Searching the tree for `CompilationUnit` handles both — but
    `finditer` does NOT yield the root itself, so the root has to be offered
    to the same filter explicitly or the single-unit shape yields nothing.
    Both halves of that are pinned by the self-test."""
    names = []
    candidates = [root] + list(root.finditer(lambda n: True))
    for cu in (n for n in candidates if n.kind_name == "CompilationUnit"):
        try:
            name = cu.p_decl.p_defining_name
            names.append(name.text if name is not None else "?")
        except Exception:                          # noqa: BLE001
            names.append("?")
    return names


def census_file(ctx, path, display, tmpdir):
    norm, crlf = normalized(path, tmpdir)
    unit = ctx.get_from_file(norm, reparse=True)
    diags = [str(d) for d in unit.diagnostics]
    row = {"file": display, "crlf": crlf, "diagnostics": diags[:5],
           "diagnostic_count": len(diags)}
    if diags or unit.root is None:
        row["kinds"] = {}
        row["nodes"] = 0
        row["compilation_units"] = []
        return row
    kinds = collections.Counter(n.kind_name
                                for n in unit.root.finditer(lambda n: True))
    row["kinds"] = dict(sorted(kinds.items()))
    row["nodes"] = sum(kinds.values())
    row["compilation_units"] = unit_names(unit.root)
    return row


def build(root, limit=None, keep_files=False):
    lal = load_lal()
    paths, macro = sources(root, limit)
    if not paths:
        sys.exit("ada_construct_census: no Ada sources under %s — is this an "
                 "unpacked ACATS delivery?" % root)
    base = os.path.abspath(root if os.path.isdir(root)
                           else os.path.dirname(root))
    ctx = lal.AnalysisContext()
    rows = []
    with tempfile.TemporaryDirectory() as tmpdir:
        for path in paths:
            display = os.path.relpath(path, base)
            rows.append(census_file(ctx, path, display, tmpdir))

    union = collections.Counter()
    for r in rows:
        union.update(r["kinds"])
    if not union:
        sys.exit("ada_construct_census: ZERO node kinds over %d source(s) — "
                 "an empty census is an instrument fault, never a finding"
                 % len(rows))

    parsed = [r for r in rows if not r["diagnostic_count"]]
    # A parse diagnostic is not automatically a finding: **class B and L
    # tests contain deliberate illegalities** (ACATS User's Guide 4.2.2), so
    # a B test the frontend rejects is the corpus working as designed.  A
    # class C test that will not parse is a different matter entirely.
    # Pooling the two would make the number unreadable, so they are split by
    # the class letter the ACATS encodes in the first character of the name.
    diag_by_class = collections.Counter(
        os.path.basename(r["file"])[:1].upper()
        for r in rows if r["diagnostic_count"])
    per_file = sorted(len(r["kinds"]) for r in parsed)
    out = {
        "instrument": "harness/ada_construct_census.py",
        "language": "ada",
        "frontend": {"name": "libadalang", "version": "libadalang-26"},
        "corpus": os.path.basename(os.path.abspath(root.rstrip("/"))),
        "sources_total": len(paths),
        "sources_parsed": len(parsed),
        "sources_with_diagnostics": len(rows) - len(parsed),
        "diagnostics_by_test_class": dict(sorted(diag_by_class.items())),
        "macro_sources_excluded": len(macro),
        "crlf_sources": sum(1 for r in rows if r["crlf"]),
        "sampled": limit is not None and limit < len(paths),
        "nodes_total": sum(r["nodes"] for r in rows),
        "node_kinds_distinct": len(union),
        "node_kinds": sorted(union),
        "node_kind_counts": dict(sorted(union.items())),
        "kinds_per_file_median": (per_file[len(per_file) // 2]
                                  if per_file else 0),
        "kinds_per_file_max": per_file[-1] if per_file else 0,
    }
    if keep_files:
        out["files"] = rows
    return out


SELF_TEST_SRC = """\
package Selftest is
   subtype Small is Integer range 1 .. 5;
   procedure P (X : Integer);
   procedure Q (Y : Integer);
   function F (Z : Integer) return Integer;
   Flag : constant Boolean := False;
end Selftest;
"""

SELF_TEST_BAD = "package Broken is\n   procedure ;;;\n"


def self_test():
    """The shapes that would produce a WRONG answer rather than no answer:
    a source with parse diagnostics (libadalang returns a partial tree, and
    counting it would be the clang mistake), a `.tst` macro file that is not
    Ada, and a CRLF source."""
    load_lal()
    ok = True
    with tempfile.TemporaryDirectory() as d:
        with open(os.path.join(d, "selftest.ada"), "w") as fh:
            fh.write(SELF_TEST_SRC)
        with open(os.path.join(d, "crlf.ada"), "wb") as fh:
            fh.write(SELF_TEST_SRC.replace("\n", "\r\n").encode())
        with open(os.path.join(d, "broken.ada"), "w") as fh:
            fh.write(SELF_TEST_BAD)
        with open(os.path.join(d, "macro.tst"), "w") as fh:
            fh.write("package M is $BIG_INT; end M;\n")
        out = build(d, keep_files=True)
        rows = {r["file"]: r for r in out["files"]}
        checks = [
            ("sources counted", out["sources_total"], 3),
            ("macro file EXCLUDED", out["macro_sources_excluded"], 1),
            ("crlf source detected", out["crlf_sources"], 1),
            ("broken source is not counted as a small program",
             out["sources_with_diagnostics"], 1),
            ("broken source contributes no kinds",
             rows["broken.ada"]["kinds"], {}),
            ("crlf parses to the SAME kinds as lf",
             rows["crlf.ada"]["kinds"] == rows["selftest.ada"]["kinds"], True),
            ("unit name read from the TREE, not the path",
             rows["selftest.ada"]["compilation_units"], ["Selftest"]),
            ("SubpDecl found", rows["selftest.ada"]["kinds"].get("SubpDecl"), 3),
        ]
        for name, got, want in checks:
            if got != want:
                ok = False
            print("%s %-52s got %r want %r"
                  % ("ok " if got == want else "FAIL", name, got, want))
    print("self-test:", "PASSED" if ok else "FAILED")
    return 0 if ok else 1


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("path", nargs="?")
    ap.add_argument("-o", "--output")
    ap.add_argument("--compare", help="a previous census JSON; report the delta")
    ap.add_argument("--limit", type=int, help="census only the first N sources")
    ap.add_argument("--files", action="store_true",
                    help="include the per-file rows (large)")
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()

    if args.self_test:
        return self_test()
    if not args.path:
        sys.exit("ada_construct_census: a directory or file is required")
    if not os.path.exists(args.path):
        sys.exit("ada_construct_census: no such path: %s" % args.path)

    out = build(args.path, args.limit, args.files)
    text = json.dumps(out, indent=2, sort_keys=True) + "\n"

    if args.compare:
        with open(args.compare) as fh:
            old = json.load(fh)
        drift = 0
        a, b = set(old.get("node_kinds", [])), set(out["node_kinds"])
        for label, s in (("added", b - a), ("dropped", a - b)):
            if s:
                print("node kinds %s: %s" % (label, ", ".join(sorted(s))))
                drift += len(s)
        for key in ("sources_parsed", "node_kinds_distinct", "nodes_total"):
            if old.get(key) != out[key]:
                print("%-24s %s -> %s" % (key, old.get(key), out[key]))
                drift += 1
        print("compare: %d differences" % drift)
        return 1 if drift else 0

    if args.output:
        with open(args.output, "w") as fh:
            fh.write(text)
        print("Ada construct census: %d sources (%d parsed, %d with "
              "diagnostics, %d macro files excluded) | %d distinct node kinds "
              "over %d nodes"
              % (out["sources_total"], out["sources_parsed"],
                 out["sources_with_diagnostics"], out["macro_sources_excluded"],
                 out["node_kinds_distinct"], out["nodes_total"]))
    else:
        sys.stdout.write(text)
    return 0


if __name__ == "__main__":
    sys.exit(main())
