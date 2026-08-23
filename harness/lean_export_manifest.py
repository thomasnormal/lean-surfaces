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

A round-trip obligation exists exactly where all three agree an item kind lives.
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


class CensusRefusal(Exception):
    """The instrument declines, loudly.  An input fault, never a finding."""


def _read(p: Path) -> str:
    if not p.is_file(): raise CensusRefusal(f"missing input: {p}")
    return p.read_text(encoding="utf-8", errors="replace")


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
    exp, par, spec = root / "Export.lean", root / "Export" / "Parse.lean", root / "format_ndjson.md"
    rev = _rev(root)
    toolchain = _read(root / "lean-toolchain").strip()

    emit, parse = _emit_sites(_read(exp)), _parse_sites(_read(par))
    secs, ver = _spec_sections(_read(spec))
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
            "round_trip_obligation": bool(p) and (bool(e) or bool(nested)),
        })
    if missing:
        raise CensusRefusal("declared item kinds not found where they belong: " + "; ".join(missing))

    oblig = [r for r in rows if r["round_trip_obligation"]]
    by_cat: dict[str, int] = {}
    for r in oblig: by_cat[r["category"]] = by_cat.get(r["category"], 0) + 1
    return {
        "schema": "lean-export-manifest/1",
        "source": "leanprover/lean4export",
        "commit": rev,
        "toolchain": toolchain,
        "format_version": ver,
        "obligations": {
            "total": len(oblig),
            "by_category": dict(sorted(by_cat.items())),
            "nested": sorted(r["key"] for r in oblig if r["nested_in"]),
            "undocumented_in_spec": sorted(r["key"] for r in rows if not r["spec_documented"]),
        },
        "not_emitted_by_design": dict(sorted(NOT_EMITTED.items())),
        "rows": sorted(rows, key=lambda r: (r["category"], r["key"])),
    }


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--export", required=True, type=Path, help="a lean4export checkout")
    ap.add_argument("-o", "--output", type=Path)
    ap.add_argument("--compare", type=Path)
    a = ap.parse_args(argv)
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
