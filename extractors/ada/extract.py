#!/usr/bin/env python3
"""extract.py — Ada source -> the `ada-0.1` envelope.

Mirrors `extractors/c/extract.py` and `extractors/python/extract.py`.
`docs/ada-envelope-schema.md` is normative for the shape; this file does not
get to invent one, and where it would have been cheaper to deviate it says so
instead (§the span shape, below).

    python3 extractors/ada/extract.py <source>... -o out.json
    python3 extractors/ada/extract.py <source> --source-name acats42/c3/c324001.a
    python3 extractors/ada/extract.py <b-test> --allow-diagnostics
    python3 extractors/ada/extract.py --self-test

CONTRACT, unchanged from the other lanes: it **never fails on valid Ada**.
Anything outside the pinned vocabulary becomes an `Unsupported` leaf carrying
libadalang's own node class and <=200 characters of source. Hard errors — an
unreadable file, a parse diagnostic without `--allow-diagnostics`, a missing
vocabulary file — exit non-zero and say why.

THE FOUR THINGS THIS EXTRACTOR HAS TO GET RIGHT, all of them measured
hazards rather than anticipated ones:

1. **`compilation_units` is read from the TREE, never derived from the path.**
   Measured over the whole ACATS delivery: **680 of 4,810 files — one in
   seven — have a name that is not among their unit names**, 723 declare more
   than one unit, 383 contain child units (`docs/backlog.md` §L74). This is
   `docs/backlog.md` §L67's mistake, and in Ada it is the common case.

2. **The parse tree's ROOT SHAPE DIFFERS BY FILE.** A source with ONE
   compilation unit parses to a root whose own kind is `CompilationUnit`;
   a source with SEVERAL parses to a `CompilationUnitList`. And `finditer`
   does NOT yield the root itself. Getting either wrong produces a silently
   wrong answer that looks like a working extractor on multi-unit files.
   Both are the self-test's first two cases.

3. **The ACATS markings come out of the COMMENTS**, with the ACAA's own
   RANGE INDICATOR arithmetic (User's Guide 6.3.2), because they are the
   expected result of 37.1% of the suite and an AST discards them. The rule
   is implemented from the spec and CHECKED against the ACAA's own `SUMMARY`
   tool by `harness/ada_round_trip.py`.

4. **CRLF is converted before parsing and RECORDED**, because the ZIP
   delivery ships CRLF and the ACAA's own tools die on it (§L69).

THE SPAN SHAPE, and why it is not the cheap one. `docs/ada-envelope-schema.md`
§2 fixes spans as an OBJECT with four named keys, which costs roughly three
times what a 4-element array would. Deviating here would have been the exact
drift the schema's own §5 gate exists to catch, so the schema wins and this
note stands in place of the deviation.

Python >= 3.9 plus libadalang.  Deterministic: sorted where order is not
semantic, byte-identical on a double run.
"""

import argparse
import hashlib
import json
import os
import re
import sys
import tempfile

SCHEMA_VERSION = "ada-0.1"
DEFAULT_VOCAB = "docs/ada-construct-census.json"
DEFAULT_LANGUAGE_VERSION = "Ada2012"
DEFAULT_PROFILE_ID = "ada-profile-0.1"
FRONTEND = {"name": "libadalang", "version": "libadalang-26"}
UNSUPPORTED_TEXT_LIMIT = 200

# ACATS marking vocabulary (User's Guide 4.2.2, 4.2.6).  Ordered longest-first
# so `OPTIONAL ERROR:` is not read as `ERROR:`.
MARKINGS = [
    ("OPTIONAL ERROR", re.compile(r"--\s*OPTIONAL\s+ERROR:?")),
    ("POSSIBLE ERROR", re.compile(r"--\s*POSSIBLE\s+ERROR:")),
    ("ANX-C RQMT", re.compile(r"--\s*ANX-C\s+RQMT")),
    ("ERROR", re.compile(r"--\s*ERROR:")),
    ("OK", re.compile(r"--\s*OK\b")),
]

# The range indicator, User's Guide 6.3.2:  {[sl:]sp[;[el:]ep]}
# sl/el are offsets BEFORE the current line; sp is an absolute position in
# that line; ep is an offset BACK FROM the last significant character.
RANGE = re.compile(r"\{(?:(-?\d+):)?(-?\d+)(?:;(?:(-?\d+):)?(-?\d+))?\}\s*$")

ACQUIRE = ("extract: libadalang is not importable.  Run "
           "`python3 harness/ada_toolchain_census.py` for the acquisition "
           "path and the exact environment — the bindings are ctypes over a "
           "SHARED library, so PYTHONPATH needs the bindings' PARENT and "
           "DYLD_LIBRARY_PATH (or LD_LIBRARY_PATH) needs every built "
           "dependency's directory.  Note `nice` is SIP-protected on macOS "
           "and STRIPS DYLD_*: use `nice -n N env DYLD_LIBRARY_PATH=... python3`.")


def load_lal():
    try:
        import libadalang as lal
    except Exception as exc:                       # noqa: BLE001 — reported
        sys.exit("%s\n  underlying error: %s" % (ACQUIRE, exc))
    return lal


def load_vocab(path):
    if path is None:
        return None
    if not os.path.exists(path):
        sys.exit("extract: vocabulary file not found: %s — it is produced by "
                 "harness/ada_construct_census.py, and the schema's §3 makes "
                 "it the single source of truth for what the ingester "
                 "accepts" % path)
    with open(path) as fh:
        kinds = json.load(fh).get("node_kinds")
    if not kinds:
        sys.exit("extract: %s carries no `node_kinds` — an empty vocabulary "
                 "would make every node Unsupported, which is an instrument "
                 "fault and not a finding" % path)
    return set(kinds)


def last_significant_col(line):
    """The last non-whitespace character that is not part of a comment —
    the ACAA's own wording (User's Guide 6.3.2)."""
    code = line.split("--", 1)[0]
    stripped = code.rstrip()
    return len(stripped)


def first_col(line):
    code = line.split("--", 1)[0]
    return len(code) - len(code.lstrip()) + 1


def marking_span(lines, lineno, raw):
    """Apply the range indicator if present, else the whole code on the line.

    Derived from User's Guide 6.3.2 and CHECKED against the ACAA's own
    SUMMARY tool: 10 of 10 exact on `B324001.A`, including the `{12;3}`
    forms, before this was written."""
    m = RANGE.search(raw.rstrip())
    if not m:
        return {"line": lineno, "col": first_col(lines[lineno - 1]),
                "end_line": lineno,
                "end_col": last_significant_col(lines[lineno - 1])}
    sl = int(m.group(1) or 0)
    sp = int(m.group(2))
    el = int(m.group(3) or 0)
    ep = int(m.group(4) or 0)
    start_line = lineno - sl
    end_line = lineno - el
    end_ref = lines[end_line - 1] if 1 <= end_line <= len(lines) else ""
    return {"line": start_line, "col": sp, "end_line": end_line,
            "end_col": last_significant_col(end_ref) - ep}


def markings_of(text, file_index):
    lines = text.split("\n")
    out = []
    for i, raw in enumerate(lines, 1):
        for kind, pat in MARKINGS:
            m = pat.search(raw)
            if not m:
                continue
            note = raw[m.end():].strip()
            note = RANGE.sub("", note).strip()
            span = marking_span(lines, i, raw)
            out.append({"kind": kind, "file": file_index, "text": note[:120],
                        **span})
            break
    out.sort(key=lambda r: (r["file"], r["line"], r["col"], r["kind"]))
    return out


def span_of(node):
    s = node.sloc_range
    return {"line": s.start.line, "col": s.start.column,
            "end_line": s.end.line, "end_col": s.end.column}


def encode(node, vocab, counter):
    """One libadalang node -> its envelope form.  A null child is preserved
    as `null`, because in Ada an ABSENT optional field is meaningful — a
    missing default expression is not the same program as a present one."""
    if node is None:
        return None
    kind = node.kind_name
    if vocab is not None and kind not in vocab:
        counter[0] += 1
        return {"kind": "Unsupported", "node_class": kind,
                "text": node.text[:UNSUPPORTED_TEXT_LIMIT],
                "span": span_of(node)}
    children = list(node.children)
    row = {"kind": kind, "span": span_of(node)}
    if children:
        row["children"] = [encode(c, vocab, counter) for c in children]
    else:
        row["text"] = node.text
    return row


def compilation_units(root):
    """Every `CompilationUnit`, in SOURCE order.

    The root shape differs by file and `finditer` does not yield the root,
    so the root is offered to the same filter explicitly (§2 of this file's
    header)."""
    candidates = [root] + list(root.finditer(lambda n: True))
    return [n for n in candidates if n.kind_name == "CompilationUnit"]


def unit_name(cu):
    try:
        name = cu.p_decl.p_defining_name
        return name.text if name is not None else None
    except Exception:                              # noqa: BLE001
        return None


def unit_kind(cu):
    try:
        return cu.p_decl.kind_name
    except Exception:                              # noqa: BLE001
        return None


def order_of(path):
    """The compilation ORDER, from the eighth character of the ACATS name
    where it has one (User's Guide 4.3.1/4.3.2: position 8 is the
    compilation sequence identifier, `0` first).  Files without one keep
    their position in the argument list, which the caller supplies."""
    stem = os.path.splitext(os.path.basename(path))[0]
    if len(stem) >= 8 and stem[7].isdigit():
        return int(stem[7])
    return None


def extract(paths, vocab, source_names=None, language_version=None,
            profile_id=None, allow_diagnostics=False):
    lal = load_lal()
    ctx = lal.AnalysisContext()
    source_files, units, marks, diagnostics = [], [], [], []
    counter = [0]
    with tempfile.TemporaryDirectory() as tmpdir:
        for index, path in enumerate(paths):
            try:
                with open(path, "rb") as fh:
                    data = fh.read()
            except OSError as exc:
                sys.exit("extract: cannot read %s: %s" % (path, exc))
            crlf = b"\r\n" in data
            normalized = data.replace(b"\r\n", b"\n")
            name = (source_names[index] if source_names
                    else os.path.basename(path))
            source_files.append({
                "path": name,
                "sha256": hashlib.sha256(data).hexdigest(),
                "line_endings": "crlf" if crlf else "lf"})
            tmp = os.path.join(tmpdir, "%03d-%s" % (index,
                                                    os.path.basename(path)))
            with open(tmp, "wb") as fh:
                fh.write(normalized)
            unit = ctx.get_from_file(tmp, reparse=True)
            for d in unit.diagnostics:
                diagnostics.append({"file": index, "message": str(d)})
            text = normalized.decode("utf-8", "replace")
            marks.extend(markings_of(text, index))
            if unit.root is None:
                continue
            explicit = order_of(path)
            for position, cu in enumerate(compilation_units(unit.root)):
                units.append({
                    "name": unit_name(cu),
                    "kind": unit_kind(cu),
                    "file": index,
                    "order": explicit if explicit is not None else index,
                    "position": position,
                    "span": span_of(cu),
                    "decl": encode(cu, vocab, counter)})

    if diagnostics and not allow_diagnostics:
        sys.exit("extract: %d parse diagnostic(s), first: %s\n  A class B or "
                 "L test is EXPECTED to be illegal — pass --allow-diagnostics "
                 "for those.  On any other class this is a finding."
                 % (len(diagnostics), diagnostics[0]["message"]))

    units.sort(key=lambda u: (u["order"], u["file"], u["position"]))
    marks.sort(key=lambda r: (r["file"], r["line"], r["col"], r["kind"]))
    return {
        "schema_version": SCHEMA_VERSION,
        "language": "ada",
        "language_version": language_version or DEFAULT_LANGUAGE_VERSION,
        "frontend": FRONTEND,
        "profile_id": profile_id or DEFAULT_PROFILE_ID,
        "source_files": source_files,
        "compilation_units": units,
        "markings": marks,
        "diagnostics": diagnostics,
        "unsupported_count": counter[0],
        "lean_blocks": [],
    }


SELF_TEST = {
    # ONE compilation unit: root kind is `CompilationUnit` itself.
    "single.ada": "package Single is\n   procedure P;\nend Single;\n",
    # TWO: root kind is `CompilationUnitList`.  Same extractor, both shapes.
    "double.ada": ("package Double is\n   procedure P;\nend Double;\n\n"
                   "package body Double is\n   procedure P is\n"
                   "   begin\n      null;\n   end P;\nend Double;\n"),
    # The unit name is NOT the file name, which in ACATS is one file in seven.
    "b3710010.a": "package B371001_0 is\n   X : Integer := 1;\nend B371001_0;\n",
}


def self_test():
    load_lal()
    ok = True
    with tempfile.TemporaryDirectory() as d:
        paths = {}
        for name, body in SELF_TEST.items():
            p = os.path.join(d, name)
            with open(p, "w") as fh:
                fh.write(body)
            paths[name] = p
        # A CRLF copy of `single.ada`, and a marked-up B-test fragment whose
        # range indicator is the one checked against the ACAA's own tool.
        crlf = os.path.join(d, "crlf.ada")
        with open(crlf, "wb") as fh:
            fh.write(SELF_TEST["single.ada"].replace("\n", "\r\n").encode())
        marked = os.path.join(d, "marked.ada")
        with open(marked, "w") as fh:
            fh.write("package Marked is\n"
                     "      X : Integer := True;           -- ERROR: (A)  {12;1}\n"
                     "      Y : Integer := 1;              -- OK.\n"
                     "end Marked;\n")

        one = extract([paths["single.ada"]], None)
        two = extract([paths["double.ada"]], None)
        named = extract([paths["b3710010.a"]], None)
        crlf_env = extract([crlf], None)
        mk = extract([marked], None, allow_diagnostics=True)

        checks = [
            ("single-unit root shape yields 1 unit",
             len(one["compilation_units"]), 1),
            ("multi-unit root shape yields 2 units",
             len(two["compilation_units"]), 2),
            ("unit NAME is read from the tree, not the file name",
             named["compilation_units"][0]["name"], "B371001_0"),
            ("...and the file name is indeed different",
             os.path.splitext("b3710010.a")[0].upper()
             != named["compilation_units"][0]["name"].upper(), True),
            ("order comes from the 8th character",
             named["compilation_units"][0]["order"], 0),
            ("crlf is recorded", crlf_env["source_files"][0]["line_endings"],
             "crlf"),
            ("crlf sha256 is of the ORIGINAL bytes",
             crlf_env["source_files"][0]["sha256"]
             != one["source_files"][0]["sha256"], True),
            ("crlf parses to the same unit count",
             len(crlf_env["compilation_units"]), 1),
            ("markings found", [m["kind"] for m in mk["markings"]],
             ["ERROR", "OK"]),
            # `      X : Integer := True;` puts its last significant
            # character (the `;`) at column 26, so `{12;1}` is col 12 and
            # end_col 26-1 = 25.  These numbers were WRONG on the first
            # write and the self-test caught the author's arithmetic, not
            # the code's — which is the direction that check is for.
            ("range indicator arithmetic",
             (mk["markings"][0]["col"], mk["markings"][0]["end_col"]),
             (12, 25)),
            # No indicator: the whole code on the line, columns 7..23.
            ("un-indicated marking spans the code",
             (mk["markings"][1]["col"], mk["markings"][1]["end_col"]),
             (7, 23)),
            ("every node carries a CERR-grade span",
             all(k in one["compilation_units"][0]["decl"]["span"]
                 for k in ("line", "col", "end_line", "end_col")), True),
            ("schema version is the one the schema fixes",
             one["schema_version"], SCHEMA_VERSION),
        ]
        # Vocabulary: an out-of-vocab kind becomes an Unsupported leaf.
        tiny = extract([paths["single.ada"]], {"CompilationUnit"})
        checks.append(("out-of-vocab kinds become Unsupported leaves",
                       tiny["unsupported_count"] > 0, True))
        checks.append(("...and the leaf names the frontend's own class",
                       tiny["compilation_units"][0]["decl"]["children"][1]
                       ["node_class"], "LibraryItem"))
        # Determinism.
        checks.append(("double run is byte-identical",
                       json.dumps(extract([paths["double.ada"]], None),
                                  sort_keys=True) == json.dumps(two,
                                                                sort_keys=True),
                       True))
        for name, got, want in checks:
            if got != want:
                ok = False
            print("%s %-50s got %r want %r"
                  % ("ok " if got == want else "FAIL", name, got, want))
    print("self-test:", "PASSED" if ok else "FAILED")
    return 0 if ok else 1


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("sources", nargs="*")
    ap.add_argument("-o", "--output")
    ap.add_argument("--vocab", default=DEFAULT_VOCAB,
                    help="the census JSON whose node_kinds is the vocabulary; "
                         "'none' disables the check")
    ap.add_argument("--source-name", action="append",
                    help="the SPELLING to record for each source, in order — "
                         "the corpus is cross-repo and a path relative to "
                         "this root would be a fiction")
    ap.add_argument("--language-version", default=DEFAULT_LANGUAGE_VERSION)
    ap.add_argument("--profile-id", default=DEFAULT_PROFILE_ID)
    ap.add_argument("--allow-diagnostics", action="store_true",
                    help="a class B or L test is EXPECTED to be illegal")
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()

    if args.self_test:
        return self_test()
    if not args.sources:
        sys.exit("extract: at least one Ada source is required")
    for path in args.sources:
        if not os.path.isfile(path):
            sys.exit("extract: no such file: %s" % path)
    if args.source_name and len(args.source_name) != len(args.sources):
        sys.exit("extract: --source-name given %d time(s) for %d source(s) — "
                 "the recorded spelling is part of the envelope and a "
                 "mismatched list would silently mis-label one"
                 % (len(args.source_name), len(args.sources)))

    vocab = None if args.vocab == "none" else load_vocab(args.vocab)
    out = extract(args.sources, vocab, args.source_name,
                  args.language_version, args.profile_id,
                  args.allow_diagnostics)
    text = json.dumps(out, indent=2, sort_keys=True) + "\n"
    if args.output:
        with open(args.output, "w") as fh:
            fh.write(text)
        print("%s: %d source(s), %d compilation unit(s), %d marking(s), "
              "%d unsupported, %d diagnostic(s)"
              % (os.path.basename(args.output), len(out["source_files"]),
                 len(out["compilation_units"]), len(out["markings"]),
                 out["unsupported_count"], len(out["diagnostics"])))
    else:
        sys.stdout.write(text)
    return 0


if __name__ == "__main__":
    sys.exit(main())
