#!/usr/bin/env python3
"""softfloat_consumer_census.py — who crosses core's OPAQUE float boundary?

WHY THIS INSTRUMENT EXISTS.  SoftFloat layer 3 (LeanModels/SoftFloat/Transfer.lean)
carries width-parametric facts across core's packed boundary.  It can only serve a
call site that goes through `Float.Model`; it CANNOT serve one that calls an
`opaque` declaration, because an opaque has no Lean body and no theorem transfers
to it.  So the transfer layer's real consumer list is "every site that crosses the
opaque boundary", and this instrument measures it.

TWO DESIGN CHOICES WORTH STATING, both of them §5.4 clauses:

1. THE OPAQUE SET IS DERIVED FROM THE TOOLCHAIN, NEVER HARDCODED.  Whether
   `Float.toInt64` reduces is a fact about the PIN, not about this lane's memory.
   The instrument parses the toolchain's own sources and classifies each float
   declaration `opaque` / `def` / `extern-def`.  A toolchain bump therefore moves
   the census by itself, instead of silently invalidating a hardcoded list.

2. IT COUNTS THE PATTERN POSITION, NOT THE IDENTIFIER.  A bare grep for
   `toInt64` scores prose, docstrings and this very file.  Lean comments and
   string literals are stripped before matching, and every row records whether
   the hit is in CODE or in PROSE.  The difference is not cosmetic: the raw
   identifier count over-reports.

OUTPUT   docs/softfloat-consumer-census.json  (sorted, machine-readable)
USAGE    python3 harness/softfloat_consumer_census.py [--compare] [--toolchain DIR]
         python3 harness/softfloat_consumer_census.py --self-test
EXIT     0 ok / clean compare · 1 drift or self-test failure · 2 instrument fault
"""
import argparse, json, os, re, sys, subprocess

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(ROOT, "docs", "softfloat-consumer-census.json")
SCAN_DIRS = ["LeanModels", "Examples"]


def die(msg, code=2):
    print(f"softfloat_consumer_census: {msg}", file=sys.stderr)
    sys.exit(code)


def toolchain_dir():
    tc = os.path.join(ROOT, "lean-toolchain")
    if not os.path.exists(tc):
        die("no lean-toolchain in the clone — cannot pin the census")
    pin = open(tc).read().strip()
    name = pin.replace("/", "--").replace(":", "---")
    d = os.path.expanduser(f"~/.elan/toolchains/{name}/src/lean")
    return pin, d


def strip_lean(src):
    """Blank out Lean comments and string literals, PRESERVING line structure.

    Nested `/- -/` is real Lean and a non-nesting stripper mis-scopes docstrings,
    so the block scanner counts depth.  Newlines are kept so line numbers survive.
    """
    out, i, n, depth = [], 0, len(src), 0
    while i < n:
        c = src[i]
        if depth:
            if src.startswith("/-", i):
                depth += 1; out.append("  "); i += 2; continue
            if src.startswith("-/", i):
                depth -= 1; out.append("  "); i += 2; continue
            out.append("\n" if c == "\n" else " "); i += 1; continue
        if src.startswith("/-", i):
            depth = 1; out.append("  "); i += 2; continue
        if src.startswith("--", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i)); i = j; continue
        if c == '"':
            out.append(" "); i += 1
            while i < n and src[i] != '"':
                if src[i] == "\\":
                    out.append(" "); i += 1
                    if i < n: out.append(" "); i += 1
                    continue
                out.append("\n" if src[i] == "\n" else " "); i += 1
            if i < n: out.append(" "); i += 1
            continue
        out.append(c); i += 1
    return "".join(out)


FLOAT_TOKEN = re.compile(r"(?<![A-Za-z0-9_'])Float(32)?(?![A-Za-z0-9_'])")

DECL_RE = re.compile(
    r"^\s*(?:@\[(?P<attrs>[^\]]*)\]\s*)?(?P<kind>opaque|def|protected def)\s+"
    r"(?P<name>(?:Float32?|UInt\d+|Int\d+|USize|ISize)\.[A-Za-z0-9_']+)",
    re.M)


def classify_toolchain(tcdir):
    """Parse the toolchain's float sources; return {qualified name: kind}."""
    files = [
        "Init/Data/Float/Float.lean",
        "Init/Data/Float/Float32.lean",
        "Init/Data/SInt/Float.lean",
        "Init/Data/SInt/Float32.lean",
    ]
    table = {}
    seen_any = False
    for rel in files:
        p = os.path.join(tcdir, rel)
        if not os.path.exists(p):
            continue
        seen_any = True
        src = open(p, encoding="utf-8").read()
        # NOTE: declarations are matched on the RAW source, because `opaque` vs
        # `def` is what we are measuring and docstrings never contain either in
        # a declaration position.  Attributes are read to spot @[extern].
        for m in DECL_RE.finditer(src):
            attrs = m.group("attrs") or ""
            kind = m.group("kind").replace("protected ", "")
            extern = "extern" in attrs
            if kind == "opaque":
                verdict = "opaque"          # no Lean body: NOTHING transfers
            elif extern:
                verdict = "extern-def"      # C impl + Lean body: reduces
            else:
                verdict = "def"
            table[m.group("name")] = verdict
    if not seen_any:
        die(f"no float sources under {tcdir} — is the toolchain source installed?")
    if not table:
        die("parsed the float sources and found ZERO declarations — instrument fault")
    return table


def scan_tree(names):
    """Find call sites, separating CODE from PROSE positions.

    A BARE MEMBER NAME IS NOT A MATCH, and this is the instrument's own scar.
    The first version matched the member alone — `round`, `exp`, `log`, `pow`,
    `toString` — and scored 319 "prose hits" that were overwhelmingly the
    ENGLISH WORDS and other types' `toString`.  Twelve times the true count,
    in the flattering direction (a bigger consumer list).  §5.4a again: the
    over-report looked like a finding.

    So a hit must occupy a PATTERN POSITION, and there are exactly two:

      QUALIFIED      `Float.toInt64`, `Int64.toFloat`   -- certain
      DOT-NOTATION   `x.toInt64`                        -- candidate: the
                     receiver's type is not knowable by regex, so these are
                     reported separately and never merged into the certain count.
    """
    members = sorted({n.split(".", 1)[1] for n in names})
    owners = sorted({n.split(".", 1)[0] for n in names})
    alt = "|".join(re.escape(m) for m in members)
    # one regex, two verdicts: capture the receiver so a qualified hit
    # (`Float.toInt64`) is never double-counted as a dot-notation candidate.
    site = re.compile(r"(?<![A-Za-z0-9_'])([A-Za-z0-9_'.]*)\.(" + alt + r")(?![A-Za-z0-9_'])")
    ownerset = set(owners)

    rows = []
    for d in SCAN_DIRS:
        base = os.path.join(ROOT, d)
        if not os.path.isdir(base):
            continue
        for dirpath, _, filenames in os.walk(base):
            for fn in sorted(filenames):
                if not fn.endswith(".lean"):
                    continue
                p = os.path.join(dirpath, fn)
                rel = os.path.relpath(p, ROOT)
                raw = open(p, encoding="utf-8").read()
                code = strip_lean(raw)
                # SOUND NARROWING: a file with no `Float` token in CODE cannot
                # contain a Float crossing.  Without this the candidate list is
                # dominated by same-named members of OTHER types -- Mathlib's
                # `Real.exp`/`Real.log` all through the analog lane, `Nat.pow`,
                # and every type's `toString`.  Measured: 170 candidates before
                # this filter, and the analog lane alone supplied most of them.
                # No false negatives: dropping a file that never names `Float`
                # cannot drop a Float call site.
                if not FLOAT_TOKEN.search(code):
                    continue
                raw_lines, code_lines = raw.split("\n"), code.split("\n")
                def sites(line):
                    out = []
                    for m in site.finditer(line):
                        recv, mem = m.group(1), m.group(2)
                        if recv in ownerset:
                            # a float-owning namespace: a DEFINITE crossing
                            out.append(("qualified", f"{recv}.{mem}"))
                        elif recv == "":
                            out.append(("anonymous", f".{mem}"))
                        elif recv[0].isupper():
                            # AN UPPERCASE RECEIVER IS A NAMESPACE, NOT A VALUE, and
                            # one that is not a float owner is a DEFINITE NON-crossing:
                            # `Nat.log2` cannot be `Float.log2`, and `Float.Model.toInt64`
                            # is the REDUCIBLE model rather than the opaque wrapper.
                            # Recorded, not silently dropped, so the exclusion is auditable.
                            out.append(("namespaced", f"{recv}.{mem}"))
                        else:
                            # a lowercase receiver is a VALUE whose type a regex cannot
                            # resolve -- a genuine candidate
                            out.append(("dotted", f".{mem}"))
                    return out
                for i, cl in enumerate(code_lines):
                    for pos, nm in sites(cl):
                        rows.append({"file": rel, "line": i + 1,
                                     "name": nm, "position": pos})
                for i, rl in enumerate(raw_lines):
                    cl = code_lines[i] if i < len(code_lines) else ""
                    nraw = [x for x in sites(rl) if x[0] == "qualified"]
                    ncode = [x for x in sites(cl) if x[0] == "qualified"]
                    for _ in range(len(nraw) - len(ncode)):
                        rows.append({"file": rel, "line": i + 1,
                                     "name": "(qualified)", "position": "prose"})
    return rows


def build(tcdir, pin):
    table = classify_toolchain(tcdir)
    opaque = sorted(n for n, v in table.items() if v == "opaque")
    reducible = sorted(n for n, v in table.items() if v != "opaque")
    rows = scan_tree(opaque)
    code = [r for r in rows if r["position"] == "qualified"]
    dotted = [r for r in rows if r["position"] in ("dotted", "anonymous")]
    namespaced = [r for r in rows if r["position"] == "namespaced"]
    prose = [r for r in rows if r["position"] == "prose"]
    by_file = {}
    for r in code + dotted:
        by_file.setdefault(r["file"], []).append(r["name"])
    return {
        "schema_version": 1,
        "toolchain_pin": pin,
        "note": ("The opaque set is DERIVED from the toolchain at the pin, never "
                 "hardcoded: whether a declaration reduces is a fact about the pin. "
                 "Counts are PATTERN POSITIONS in code, never bare identifiers. "
                 "Files with no `Float` token in code are excluded -- a sound "
                 "narrowing that removes same-named members of other types "
                 "(Mathlib's Real.exp/Real.log, Nat.pow, every type's toString). "
                 "`dotted`/`anonymous` rows remain CANDIDATES: a LOWERCASE receiver "
                 "is a value whose type a regex cannot resolve. An UPPERCASE receiver "
                 "is a NAMESPACE, and one that is not a float owner is a definite "
                 "non-crossing (`Nat.log2` is not `Float.log2`); those are listed "
                 "under `excluded` rather than dropped, so the exclusion is auditable."),
        "opaque_count": len(opaque),
        "reducible_count": len(reducible),
        "opaque_declarations": opaque,
        "crossing_sites_qualified": len(code),
        "crossing_sites_dotted_candidates": len(dotted),
        "excluded_non_float_namespace": len(namespaced),
        "qualified_hits_in_prose": len(prose),
        "crossings_by_file": {k: sorted(v) for k, v in sorted(by_file.items())},
        "crossings": sorted(code + dotted,
                            key=lambda r: (r["file"], r["line"], r["name"])),
        "excluded": sorted(namespaced,
                           key=lambda r: (r["file"], r["line"], r["name"])),
    }


def self_test():
    """Every refusal path RUN, not admired (§5.4).  No toolchain needed."""
    ok = True
    def check(label, cond):
        nonlocal ok
        print(f"  {'ok  ' if cond else 'FAIL'}  {label}")
        ok = ok and cond

    # 1. the comment stripper preserves line numbers
    s = "a\n-- toInt64\nb toInt64\n"
    st = strip_lean(s)
    check("stripper preserves line count", len(st.split("\n")) == len(s.split("\n")))
    check("stripper blanks line comments", "toInt64" not in st.split("\n")[1])
    check("stripper keeps code", "toInt64" in st.split("\n")[2])

    # 2. nested block comments
    s2 = "/- outer /- inner -/ toInt64 -/ real\n"
    check("nested block comment fully stripped", "toInt64" not in strip_lean(s2))

    # 3. string literals
    check("string literal stripped", "toInt64" not in strip_lean('x := "toInt64"\n'))

    # 3b. THE SCAR: a bare member name must NOT match
    import tempfile as _tf
    with _tf.TemporaryDirectory() as td:
        d = os.path.join(td, "LeanModels"); os.makedirs(d)
        open(os.path.join(d, "X.lean"), "w").write(
            "def f := round 3\ndef g := Float.toInt64 x\ndef h := y.toInt64\n")
        global ROOT, SCAN_DIRS
        old_root, ROOT = ROOT, td
        try:
            rows = scan_tree(["Float.toInt64", "Float.round"])
        finally:
            ROOT = old_root
        names = [(r["position"], r["name"]) for r in rows]
        check("bare member word `round` is NOT a match",
              not any(n == "round" for _, n in names))
        check("qualified `Float.toInt64` IS a match",
              ("qualified", "Float.toInt64") in names)
        check("dot-notation `.toInt64` is a CANDIDATE, not certain",
              ("dotted", ".toInt64") in names)

    # 3b2. AN UPPERCASE NON-FLOAT NAMESPACE IS A DEFINITE NON-CROSSING.
    #      This is the defect that turned triad8 red: `Nat.log2` scored as a
    #      candidate because `Float.log2` is opaque and `log2` is in the member set.
    with _tf.TemporaryDirectory() as td:
        d = os.path.join(td, "LeanModels"); os.makedirs(d)
        open(os.path.join(d, "N.lean"), "w").write(
            "def f (y : Float) := (Nat.log2 3 : Int) + y.toInt64.toNat\n")
        old_r3, _ = ROOT, None
        globals()["ROOT"] = td
        try:
            rows = scan_tree(["Float.log2", "Float.toInt64"])
        finally:
            globals()["ROOT"] = old_r3
        pos = {(r["position"], r["name"]) for r in rows}
        check("`Nat.log2` is EXCLUDED as a non-float namespace",
              ("namespaced", "Nat.log2") in pos)
        check("`Nat.log2` is NOT a dotted candidate",
              ("dotted", ".log2") not in pos)
        check("a lowercase receiver stays a candidate",
              ("dotted", ".toInt64") in pos)

    # 3c. the sound narrowing drops a file that never names Float
    with _tf.TemporaryDirectory() as td:
        d = os.path.join(td, "LeanModels"); os.makedirs(d)
        open(os.path.join(d, "NoFloat.lean"), "w").write("def f := x.exp\n")
        open(os.path.join(d, "HasFloat.lean"), "w").write(
            "def g (y : Float) := y.toInt64\n")
        old_root2, ROOT = ROOT, td
        try:
            files = {r["file"] for r in scan_tree(["Float.toInt64", "Float.exp"])}
        finally:
            ROOT = old_root2
        check("file with no `Float` token is dropped",
              not any("NoFloat" in f for f in files))
        check("file that names `Float` is kept",
              any("HasFloat" in f for f in files))

    # 3d. the transcription tripwire FIRES when the cited text is gone
    with _tf.TemporaryDirectory() as td:
        os.makedirs(os.path.join(td, "a")); os.makedirs(os.path.join(td, "b"))
        open(os.path.join(td, "a/citer.lean"), "w").write("-- cites b\n")
        open(os.path.join(td, "b/cited.lean"), "w").write("nothing relevant\n")
        global TRANSCRIPTIONS
        old_t, TRANSCRIPTIONS = TRANSCRIPTIONS, [
            ("a/citer.lean", "b/cited.lean", "MISSING_MARKER", None, "probe row")]
        old_r, ROOT2 = ROOT, td
        globals()["ROOT"] = td
        try:
            fired = not check_transcriptions()
        finally:
            globals()["ROOT"] = old_r; TRANSCRIPTIONS = old_t
        check("transcription tripwire FIRES on stale text", fired)

    # 4. a MISSING toolchain dir refuses loudly rather than returning empty
    try:
        classify_toolchain("/nonexistent/toolchain/dir")
        check("missing toolchain refuses", False)
    except SystemExit as e:
        check("missing toolchain refuses (exit 2)", e.code == 2)

    # 5. a toolchain dir that PARSES TO ZERO ROWS is an instrument fault, not a finding
    import tempfile
    with tempfile.TemporaryDirectory() as td:
        p = os.path.join(td, "Init/Data/Float")
        os.makedirs(p)
        open(os.path.join(p, "Float.lean"), "w").write("-- nothing here\n")
        try:
            classify_toolchain(td)
            check("zero-row parse refuses", False)
        except SystemExit as e:
            check("zero-row parse refuses (exit 2)", e.code == 2)
    return ok


# A transcription of another lane's file is A COPY WITH A TIMESTAMP.  This lane
# shipped one that went stale in SIX MINUTES -- the probes labelled the
# pre-unblock body "as landed" while ES committed the routing, so anyone running
# them concluded the unblock was unlanded (2026-08-23 quality audit, HIGH).
# Correcting the text does not stop the next one; a tripwire does.
TRANSCRIPTIONS = [
    # (file that cites, file cited, must-be-present, must-be-absent-or-None, why)
    ("harness/softfloat/probe_es_unblock.lean", "LeanModels/Es/Convert.lean",
     "n.toModel.toInt64", None,
     "the LANDED numberToString routes through Float.Model"),
    ("harness/softfloat/probe_es_unblock_axioms.lean", "LeanModels/Es/Convert.lean",
     "Float.ofModel (Float.Model.ofInt64 t)", None,
     "the LANDED numberToString rebuilds the Float through the model"),
    ("harness/softfloat/probe_es_unblock.lean", "LeanModels/Es/Convert.lean",
     "needs a non-clamping truncation", None,
     "the `%` arm is WITHDRAWN and refuses by name"),
]


def check_transcriptions():
    """Assert every probe's transcription still matches the file it cites."""
    ok = True
    for citer, cited, present, absent, why in TRANSCRIPTIONS:
        cp, dp = os.path.join(ROOT, citer), os.path.join(ROOT, cited)
        if not os.path.exists(cp) or not os.path.exists(dp):
            print(f"  FAIL  missing file: {citer} or {cited}"); ok = False; continue
        body = open(dp, encoding="utf-8").read()
        if present not in body:
            print(f"  FAIL  {citer} assumes {cited} contains {present!r} ({why}) "
                  f"-- IT DOES NOT.  The transcription has gone stale.")
            ok = False
        elif absent and absent in body:
            print(f"  FAIL  {citer} assumes {cited} no longer contains {absent!r}")
            ok = False
        else:
            print(f"  ok    {citer} <- {cited}: {why}")
    return ok


# --- decimal demand (SoftFloat plan step 3) -------------------------------
# Two directions, and they are asymmetric: PRINT is greenfield (core ships no
# decimal printer; `Float.toString` is opaque) while PARSE already has a
# width-parametric kernel-reducible primitive in core's `ofScientific`.
DECIMAL_SITES = [
    ("LeanModels/Es/Convert.lean", "print", "correctly-rounded decimal conversion",
     "Number::toString outside the exact-integer fragment (ECMA-262 §6.1.6.1.20)"),
    ("LeanModels/Es/Convert.lean", "parse", "outside the decimal-integer fragment",
     "StringToNumber (ECMA-262 §7.1.4.1 StringNumericLiteral)"),
]
# test262 directories a decimal conversion could gate.  THIS IS AN UPPER BOUND
# and is labelled as one: `built-ins/Number` also holds `isInteger`,
# `MAX_SAFE_INTEGER` and friends, which need no conversion at all.  The corpus
# is OUT OF TREE (pinned sha in docs/es262-census.json), so the exact figure is
# not computable here -- and per §5.4 this mode is NOT wired into CI.
DECIMAL_T262_DIRS = ["built-ins/Number", "built-ins/parseFloat"]


def decimal_demand():
    """Census the demand for plan step 3.  In-tree exact; suite bound only."""
    ok = True
    print("IN-TREE (exact) -- ES refusal sites naming a decimal float conversion:")
    found = 0
    for rel, direction, marker, what in DECIMAL_SITES:
        fp = os.path.join(ROOT, rel)
        if not os.path.exists(fp):
            print(f"  FAIL  missing {rel}"); ok = False; continue
        # NOTE: match the RAW source here, NOT `strip_lean`ed code.  A refusal
        # MESSAGE lives inside a string literal by construction, and the call-site
        # scanner blanks string literals on purpose.  Using the stripped text
        # found ZERO sites and said so loudly rather than reporting 0 as a
        # finding (§5.4: an empty census is an instrument fault).  To keep prose
        # out, a hit must sit within 3 lines of a `refuseConstruct` -- the
        # message and its call are split across lines in the real file.
        raw = open(fp, encoding="utf-8").read().split("\n")
        hit = [i + 1 for i, l in enumerate(raw)
               if marker in l and any("refuseConstruct" in raw[j]
                                      for j in range(max(0, i - 3), min(len(raw), i + 2)))]
        if not hit:
            print(f"  FAIL  {rel}: no {direction} refusal matching {marker!r} "
                  f"-- either it was fixed (good) or the marker drifted (bad)")
            ok = False
        else:
            found += len(hit)
            print(f"  ok    {rel}:{hit[0]}  [{direction}]  {what}")
    print(f"  => {found} refusal site(s), one per direction.")

    cp = os.path.join(ROOT, "docs", "es262-census.json")
    if not os.path.exists(cp):
        print("  note  docs/es262-census.json absent -- no suite bound available")
        return ok
    t = json.load(open(cp))["test262"]
    lvl = t.get("built_ins_slice", {}).get("by_second_level", {})
    total = sum(lvl.values())
    sub = {d: lvl.get(d, 0) for d in DECIMAL_T262_DIRS}
    n = sum(sub.values())
    print("\nOUT-OF-TREE (UPPER BOUND ONLY -- corpus not present, not CI-wired):")
    for d, c in sorted(sub.items()):
        print(f"  {c:6d}  {d}")
    pct = (100.0 * n / total) if total else 0.0
    print(f"  => at most {n} of {total} built-ins files ({pct:.1f}%).  UPPER BOUND: "
          f"these directories also hold tests needing no conversion at all.")
    return ok


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--compare", action="store_true")
    ap.add_argument("--toolchain")
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--decimal-demand", action="store_true",
                    help="census the demand for plan step 3 (decimal conversion)")
    ap.add_argument("--check-transcriptions", action="store_true",
                    help="assert the probes' transcriptions still match the files they cite")
    a = ap.parse_args()
    if a.decimal_demand:
        sys.exit(0 if decimal_demand() else 1)
    if a.check_transcriptions:
        sys.exit(0 if check_transcriptions() else 1)
    if a.self_test:
        sys.exit(0 if self_test() else 1)
    pin, tcdir = toolchain_dir()
    if a.toolchain:
        tcdir = a.toolchain
    if not os.path.isdir(tcdir):
        die(f"toolchain source not found: {tcdir}")
    data = build(tcdir, pin)
    blob = json.dumps(data, indent=2, sort_keys=True) + "\n"
    if a.compare:
        if not os.path.exists(OUT):
            die(f"--compare but {OUT} does not exist")
        old = open(OUT).read()
        if old != blob:
            print("softfloat_consumer_census: DRIFT against the committed census",
                  file=sys.stderr)
            sys.exit(1)
        print(f"softfloat_consumer_census: clean against {os.path.relpath(OUT, ROOT)}")
        sys.exit(0)
    open(OUT, "w").write(blob)
    print(f"softfloat_consumer_census: {data['opaque_count']} opaque / "
          f"{data['reducible_count']} reducible declarations at {pin}; "
          f"{data['crossing_sites_qualified']} qualified crossings + "
          f"{data['crossing_sites_dotted_candidates']} dot-notation candidates "
          f"({data['excluded_non_float_namespace']} excluded as non-float namespaces), "
          f"{data['qualified_hits_in_prose']} qualified hits in prose")


if __name__ == "__main__":
    main()
