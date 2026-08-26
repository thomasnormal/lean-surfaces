#!/usr/bin/env python3
"""The export-envelope COVERAGE MANIFEST (family-architecture.md §5.5).

The Lean tier adopted `lean4export`'s NDJSON as its envelope rather than
hand-building one (`docs/lean-tier-charter.md` §4).  That was the right call and
it left a debt: **the envelope is upstream's, and it is unverified** — 1 710
lines, 0 theorems, 0 sorries, 22 golden-output tests.  Charter §10.5 names the
exporter explicitly among what stays trusted after a verified checker ("that last
one is the quiet one"), so verifying its round-trip removes a NAMED entry from
the reflexive capstone's trusted set.

This instrument is what that arc owes before any Lean: a §5.5 manifest with one
row per envelope ITEM KIND, joining three independent sources —

    SPEC    format_ndjson.md          the documented format
    EMIT    Export.lean               what the exporter writes
    PARSE   Export/Parse.lean         what the reference parser reads back

A round-trip obligation exists exactly where all three agree an item kind lives
AND the round-trip is not refuted by the artifact itself (see REFUTED).
Where they DISAGREE the manifest says so rather than smoothing it: an item the
spec documents but nothing parses is a gap, and an item emitted but undocumented
is a different gap.

MECHANICAL vs DECLARED, kept separate for the reason the correspondence census
learned it: the ITEM KIND TABLE below is declared and reviewable; every
presence/absence claim about it is re-derived from the three sources on each run
and the instrument REFUSES when a declared kind cannot be found where it belongs.

Matching is ANCHORED, never a bare substring — the 2026-08-23 audit's defect
class.  An emit site is `("<kind>",` at a JSON-object position; a parse site is a
`def parse<Kind>` or an explicit dispatch arm.

Reads only.  No Lean execution, no build, no tenure.
"""

from __future__ import annotations
import argparse, json, re, subprocess, sys
from pathlib import Path


# THE FORK'S DIVERGENCE TRIPWIRE.  Our fork factors a pure core out of the
# exporter (see Export.lean's header).  The divergence is defined against a
# PINNED upstream shape, so if upstream edits any of these sites the fork must go
# LOUD rather than silently diverging further.  Each entry is a substring that
# MUST still be present in the pinned upstream blob.
DIVERGENCE_BASE = "af5aa64bb914c3c2c781f378088dbd38acf4f804"
UPSTREAM_TOUCHPOINTS = {
    "Export.lean": [
        "abbrev M := ReaderT Context <| StateT State IO",
        "IO.println (s.setObjVal! namespaced idx).compress",
        "IO.println <| Json.mkObj fields |>.compress",
        "IO.println exportMetadata.compress",
    ],
    "Export/Parse.lean": [
        "abbrev M := StateT State <| IO",
        "stream : IO.FS.Stream",
        "(← get).stream.getLine",
    ],
}


class CensusRefusal(Exception):
    """The instrument declines, loudly.  An input fault, never a finding."""


def _read(p: Path) -> str:
    if not p.is_file(): raise CensusRefusal(f"missing input: {p}")
    return p.read_text(encoding="utf-8", errors="replace")


def _read_at_base(root: Path, rel: str) -> str:
    """Read a file at the PINNED UPSTREAM BASE, never from the working tree.

    The manifest describes the ENVELOPE FORMAT, which is upstream's artifact --
    our fork's pure-core refactor does not change it.  Reading the working tree
    made the manifest measure whatever branch happened to be checked out, so it
    reported DRIFT against our own edits: line numbers moved, the recorded commit
    became our branch head, and a guard that fires on its owner's commits is one
    its owner learns to ignore.  This is the SAME defect entry 15 fixed for the
    TrProj guards, recurring in the newest instrument -- which is the argument
    for making "baseline against upstream, never against ourselves" a property of
    the instrument rather than a habit of the operator.
    """
    try:
        r = subprocess.run(["git", "-C", str(root), "show", f"{DIVERGENCE_BASE}:{rel}"],
                           capture_output=True, text=True, timeout=60)
    except (OSError, subprocess.SubprocessError) as e:
        raise CensusRefusal(f"cannot read {rel} at pinned base: {e}") from e
    if r.returncode != 0:
        raise CensusRefusal(f"pinned base {DIVERGENCE_BASE[:12]} has no {rel}")
    return r.stdout


# ---------------------------------------------------------------- declared
# One row per envelope item kind.  `parse` names the `def parse<X>` expected in
# Export/Parse.lean; `nested_in` marks kinds the exporter does NOT emit at top
# level (they ride inside another item) — an asymmetry the manifest reports
# rather than hides.
ITEM_KINDS = [
    # category,      key,        parse suffix,   nested_in
    ("name",         "str",      "NameStr",      None),
    ("name",         "num",      "NameNum",      None),
    ("level",        "succ",     "LevelSucc",    None),
    ("level",        "max",      "LevelMax",     None),
    ("level",        "imax",     "LevelImax",    None),
    ("level",        "param",    "LevelParam",   None),
    ("expr",         "bvar",     "ExprBVar",     None),
    ("expr",         "sort",     "ExprSort",     None),
    ("expr",         "const",    "ExprConst",    None),
    ("expr",         "app",      "ExprApp",      None),
    ("expr",         "lam",      "ExprLam",      None),
    ("expr",         "forallE",  "ExprForallE",  None),
    ("expr",         "letE",     "ExprLetE",     None),
    ("expr",         "proj",     "ExprProj",     None),
    ("expr",         "natVal",   "ExprNatLit",   None),
    ("expr",         "strVal",   "ExprStrLit",   None),
    ("expr",         "mdata",    "ExprMdata",    None),
    ("declaration",  "axiom",    "AxiomInfo",    None),
    ("declaration",  "def",      "DefnInfo",     None),
    ("declaration",  "opaque",   "OpaqueInfo",   None),
    ("declaration",  "thm",      "ThmInfo",      None),
    ("declaration",  "quot",     "QuotInfo",     None),
    ("declaration",  "induct",   "Inductive",    None),
    # `ctors`/`recs` are PLURAL array keys inside the `induct` group, not singular
    # discriminators.  Keying them as "ctor"/"rec" produced two wrong rows on the
    # first run: `rec` reported UNDOCUMENTED (the spec documents `"recs"` at
    # format_ndjson.md:291), and `ctor` matched `("ctor", ...)` inside
    # `dumpRecRule` — a recursor rule's NAME FIELD, not the constructor
    # declaration.  That is the unanchored/first-hit-wins defect class the
    # 2026-08-23 audit named, recurring in a new instrument, and it is why the
    # emit and spec keys are now declared explicitly per row.
    ("declaration",  "ctors",    "CtorInfo",     "induct"),
    ("declaration",  "recs",     "RecInfo",      "induct"),
    ("declaration",  "types",    "InductInfo",   "induct"),
    ("aux",          "binderInfo", "BinderInfo", None),
]

# Constructors the exporter never emits because they are pre-seeded at index 0
# or rejected outright — recorded so their absence is a DATUM, not a gap.
NOT_EMITTED = {
    "anonymous": "Name.anonymous — pre-seeded at index 0 (Export.lean), unreachable! if reached",
    "zero":      "Level.zero — pre-seeded at index 0, unreachable! if reached",
    "fvar":      "Expr.fvar — panic!: cannot export free variables or metavariables",
    "mvar":      "Expr.mvar — same panic",
}

# REFUTED, NOT COUNTED (coordinator ruling, 2026-08-24).  A kind that IS emitted
# and IS parsed but whose round-trip statement is FALSE BY UPSTREAM DESIGN.  It
# is not an unproved obligation — no proof exists to be found — so counting it
# would fix the ceiling below 100% forever, "a number that can only be too low"
# with no owner able to move it.  The mirror image of the 28th obligation's
# NAMED, NOT COUNTED: that one is a live obligation deliberately held out of the
# denominator until its premise is proved, this one is a documented property of
# the artifact.  Both are declared here so the absence is a DATUM, not a gap.
#
# A refuted kind is still required to be PRESENT in both sources below — the
# claim "this round-trip is false" is only meaningful about a kind that exists.
REFUTED = {
    "mdata": (
        "Expr.mdata — parseExprMdata BINDS AND DISCARDS the metadata "
        "(`let some (.obj _dataObj) := data[\"data\"]?`) and returns `.mdata {} expr`, "
        "under upstream's own comment \"TODO: Unclear how to perfectly recover with the "
        "current output format\".  `parse (dump e) = e` is therefore FALSE for any "
        "non-empty KVMap, not merely unproved.  Also unreachable on the default path: "
        "dumpExpr strips mdata via removeMData unless --export-mdata is passed."
    ),
}


# The corner's PROVED count is derived from the fork's `Verify.lean`, which does
# NOT exist at the pinned upstream base — it is a fork addition.  So it is
# measured against the WORKING TREE and reported under its own `measured_at`,
# never folded into `obligations` (which stays upstream-base-derived).  Mixing
# two measurement bases under one number is the §5.4a defect: a figure quoted
# without the state it was taken in.
#
# The instrument can see that a theorem EXISTS.  It cannot see that it
# elaborated, or that its axioms were clean — that is a tenure's evidence, and a
# tenure is not reproducible from a source tree.  So the green is DECLARED here,
# with its fork sha and certified tree, and the count is DERIVED.  The two are
# labelled differently on purpose.
GREEN_EVIDENCE = {
    "fork_sha": "3e9d4a9",
    "certified_tree": "1055dd8fba06",
    "gate": "lake build Test Verify",
    "witness": "Built Verify (1.3s); 17 x #print axioms, no sorryAx",
    "log": "scratchpad/leantier-triad23.log",
    "note": "fork commits are LOCAL by lane charter — the fork's only remote is "
            "upstream leanprover/lean4export, and pushing there is Thomas's "
            "decision alone.  This block is the merge-side record of a tenure "
            "whose objects the lean-surfaces remote cannot hold.",
}

_PROOF_RE = re.compile(r"^theorem\s+parse(\w+)_roundtrip\b", re.M)


def _proof_sites(src: str) -> dict[str, int]:
    """`theorem parse<Suffix>_roundtrip` in the fork's Verify.lean — anchored at
    line start, so a mention inside a comment or a docstring is not a proof."""
    return {m.group(1): src[:m.start()].count("\n") + 1 for m in _PROOF_RE.finditer(src)}


def _emit_sites(src: str) -> dict[str, int]:
    """`("<kind>",` at a JSON-object position — anchored, not a bare substring."""
    out: dict[str, int] = {}
    rx = re.compile(r'\(\s*"([A-Za-z][A-Za-z0-9]*)"\s*,')
    for n, line in enumerate(src.splitlines(), start=1):
        if line.lstrip().startswith("--"): continue
        for m in rx.finditer(line):
            out.setdefault(m.group(1), n)
    return out


def _parse_sites(src: str) -> dict[str, int]:
    """`def parse<Kind>` — anchored at column 0."""
    out: dict[str, int] = {}
    rx = re.compile(r"^(?:partial\s+)?def\s+parse([A-Za-z][A-Za-z0-9]*)\b")
    for n, line in enumerate(src.splitlines(), start=1):
        m = rx.match(line)
        if m: out.setdefault(m.group(1), n)
    return out


def _spec_sections(md: str) -> tuple[dict[str, str], str]:
    """Map an item key to the nearest preceding heading in the format spec."""
    sec, out = "(preamble)", {}
    rx = re.compile(r'"([a-zA-Z][A-Za-z0-9]*)"\s*:')
    ver = ""
    for line in md.splitlines():
        h = re.match(r"^(#{1,4})\s+(.*)$", line)
        if h:
            sec = h.group(2).strip()
            m = re.search(r"version\s+([0-9.]+)", sec)
            if m: ver = m.group(1)
            continue
        for m in rx.finditer(line):
            out.setdefault(m.group(1), sec)
    return out, ver


def check_divergence(root: Path) -> dict:
    """Re-read the PINNED upstream touch points; refuse if any has moved.

    This is the transcription law applied to a fork: our divergence is stated
    against a specific upstream shape, and a shape that changed underneath us is
    a fact we must be told about, not one to discover when a proof stops making
    sense.
    """
    found, missing = {}, []
    for rel, needles in UPSTREAM_TOUCHPOINTS.items():
        try:
            r = subprocess.run(["git", "-C", str(root), "show", f"{DIVERGENCE_BASE}:{rel}"],
                               capture_output=True, text=True, timeout=60)
        except (OSError, subprocess.SubprocessError) as e:
            raise CensusRefusal(f"cannot read pinned upstream {rel}: {e}") from e
        if r.returncode != 0:
            raise CensusRefusal(
                f"pinned upstream base {DIVERGENCE_BASE[:12]} does not contain {rel} — "
                "the divergence base is gone; re-pin deliberately"
            )
        blob = r.stdout
        for needle in needles:
            (found.setdefault(rel, []).append(needle) if needle in blob
             else missing.append(f"{rel}: {needle!r}"))
    if missing:
        raise CensusRefusal(
            "UPSTREAM MOVED under this fork's divergence — these touch points are no "
            "longer present at the pinned base: " + "; ".join(missing) +
            ". The fork's header describes a shape that no longer exists; re-census before proceeding."
        )
    return {"base": DIVERGENCE_BASE, "touchpoints_verified": found,
            "total": sum(len(v) for v in found.values())}


def _rev(d: Path) -> str:
    try:
        r = subprocess.run(["git", "-C", str(d), "rev-parse", "HEAD"],
                           capture_output=True, text=True, timeout=30)
    except (OSError, subprocess.SubprocessError) as e:
        raise CensusRefusal(f"cannot read provenance at {d}: {e}") from e
    if r.returncode != 0 or not r.stdout.strip():
        raise CensusRefusal(f"--export is not a git checkout, so the manifest has no provenance: {d}")
    return r.stdout.strip()


def census(root: Path) -> dict:
    if not root.is_dir(): raise CensusRefusal(f"missing --export directory: {root}")
    # Always at the PINNED BASE -- see _read_at_base.  The manifest is about the
    # format, not about whatever branch is checked out.
    emit = _emit_sites(_read_at_base(root, "Export.lean"))
    parse = _parse_sites(_read_at_base(root, "Export/Parse.lean"))
    secs, ver = _spec_sections(_read_at_base(root, "format_ndjson.md"))
    rev = DIVERGENCE_BASE
    toolchain = _read_at_base(root, "lean-toolchain").strip()
    if not emit: raise CensusRefusal("zero emit sites parsed — an instrument fault, never a finding")
    if not parse: raise CensusRefusal("zero parse sites parsed — an instrument fault, never a finding")
    if not ver: raise CensusRefusal("no format version found in format_ndjson.md")

    rows, missing = [], []
    for cat, key, psuf, nested in ITEM_KINDS:
        e, p, s = emit.get(key), parse.get(psuf), secs.get(key)
        # A nested kind's emit site must be the plural ARRAY key inside its
        # group; a scalar field that happens to share a name is not it.
        if nested is not None and e is not None and not key.endswith("s"):
            raise CensusRefusal(
                f"{key!r} is declared nested in {nested!r} but its key is singular — "
                "a nested item is an array key, and a singular match is almost "
                "certainly a same-named field (see dumpRecRule's `ctor`)"
            )
        # A declared kind must be parseable; emit may legitimately be nested.
        if p is None: missing.append(f"{key}: no `def parse{psuf}` in Export/Parse.lean")
        if e is None and nested is None: missing.append(f"{key}: not emitted and not declared nested")
        rows.append({
            "category": cat, "key": key,
            "spec_section": s, "spec_documented": s is not None,
            "emit_line": e, "parse_fn": f"parse{psuf}", "parse_line": p,
            "nested_in": nested,
            "refuted": REFUTED.get(key),
            "round_trip_obligation": (bool(p) and (bool(e) or bool(nested))
                                      and key not in REFUTED),
        })
    if missing:
        raise CensusRefusal("declared item kinds not found where they belong: " + "; ".join(missing))

    # PROVED, from the working tree (see GREEN_EVIDENCE).
    vpath = root / "Verify.lean"
    proofs = _proof_sites(_read(vpath)) if vpath.is_file() else {}
    for r in rows:
        psuf = r["parse_fn"].removeprefix("parse")
        line = proofs.get(psuf)
        r["proof_fn"] = f"parse{psuf}_roundtrip" if line else None
        r["proof_line"] = line
    stray = [r["key"] for r in rows if r["proof_line"] and not r["round_trip_obligation"]]
    if stray:
        raise CensusRefusal(
            "a round-trip theorem exists for a kind that is NOT an obligation: "
            + ", ".join(stray) +
            " — either the exclusion is wrong or the theorem proves something else"
        )

    oblig = [r for r in rows if r["round_trip_obligation"]]
    by_cat: dict[str, int] = {}
    for r in oblig: by_cat[r["category"]] = by_cat.get(r["category"], 0) + 1
    return {
        "schema": "lean-export-manifest/1",
        "source": "leanprover/lean4export",
        "commit": rev,
        "measured_at": "pinned upstream base, not the working tree",
        "toolchain": toolchain,
        "format_version": ver,
        "obligations": {
            "total": len(oblig),
            "by_category": dict(sorted(by_cat.items())),
            "nested": sorted(r["key"] for r in oblig if r["nested_in"]),
            "undocumented_in_spec": sorted(r["key"] for r in rows if not r["spec_documented"]),
        },
        "not_emitted_by_design": dict(sorted(NOT_EMITTED.items())),
        "refuted_not_counted": dict(sorted(REFUTED.items())),
        "proofs": {
            "measured_at": "fork WORKING TREE (Verify.lean is a fork addition, "
                           "absent at the pinned base) — not the same base as `obligations`",
            "proved": sum(1 for r in oblig if r["proof_line"]),
            "of": len(oblig),
            "by_category": {c: sum(1 for r in oblig
                                   if r["category"] == c and r["proof_line"])
                            for c in sorted({r["category"] for r in oblig})},
            "unproved": sorted(r["key"] for r in oblig if not r["proof_line"]),
            "green_evidence_declared": GREEN_EVIDENCE,
        },
        "rows": sorted(rows, key=lambda r: (r["category"], r["key"])),
    }


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--export", required=True, type=Path, help="a lean4export checkout")
    ap.add_argument("-o", "--output", type=Path)
    ap.add_argument("--compare", type=Path)
    ap.add_argument("--check-divergence", action="store_true",
                    help="verify the fork's upstream touch points at the pinned base")
    a = ap.parse_args(argv)
    if a.check_divergence:
        try:
            d = check_divergence(a.export)
        except CensusRefusal as e:
            print(f"REFUSE: {e}", file=sys.stderr); return 2
        print(f"ok: {d['total']} upstream touch points intact at {d['base'][:12]}")
        return 0
    try:
        res = census(a.export)
    except CensusRefusal as e:
        print(f"REFUSE: {e}", file=sys.stderr); return 2
    text = json.dumps(res, indent=2, sort_keys=True) + "\n"
    if a.compare:
        if not a.compare.is_file():
            print(f"REFUSE: missing baseline: {a.compare}", file=sys.stderr); return 2
        old = json.loads(a.compare.read_text())
        if old == res: print(f"ok: manifest matches {a.compare}"); return 0
        for k in sorted(set(old) | set(res)):
            if old.get(k) != res.get(k): print(f"DRIFT: {k}", file=sys.stderr)
        return 1
    if a.output:
        a.output.write_text(text, encoding="utf-8"); print(f"wrote {a.output}", file=sys.stderr)
    else: sys.stdout.write(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
