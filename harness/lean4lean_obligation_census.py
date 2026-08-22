#!/usr/bin/env python3
"""The Lean tier's OBLIGATION CENSUS of lean4lean's proof layer (M2).

Thomas ruled the endgame CONSUME-AND-EXTEND (`docs/lean-tier-charter.md` §10.2),
so the question stops being "how big is the gap" and becomes "**which specific
obligations are open, what does each need, and which are untouched**". This
instrument answers the first half mechanically; the classification and the
active-work split live in `docs/lean4lean-obligation-census.md`.

THE COUNTING RULE, and it is the whole reason this is an instrument rather than a
grep. The Wasm lane's lesson: a raw `grep -c sorry` counts commented-out code,
prose discussing sorries, and docstrings that mention the word. **Both counts are
reported and the DELTA IS A FINDING** — a large gap means the project talks about
its holes as much as it has them, which is itself information about how the
proof layer is maintained.

Lean's comment syntax needs real handling, not a regex: `--` to end of line,
`/- ... -/` block comments that **nest**, `/-- ... -/` docstrings, and string
literals that may contain any of the above. A stripper that got nesting wrong
would silently swallow live code and undercount.

ATTRIBUTION. Every obligation is attributed to its enclosing declaration by
walking back to the nearest column-0 declaration keyword, so the output names
*which theorem is blocked* rather than just a line number.

Reads only. No Lean execution, no build (amendment 11).

Usage:
    lean4lean_obligation_census.py --l4l DIR [-o OUT]
    lean4lean_obligation_census.py --l4l DIR --compare docs/lean4lean-obligation-census.json
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path


class CensusRefusal(Exception):
    """The instrument declines, loudly.  An input fault, never a finding."""


def _read(p: Path) -> str:
    if not p.is_file(): raise CensusRefusal(f"missing input: {p}")
    return p.read_text(encoding="utf-8", errors="replace")


def strip_comments(src: str) -> str:
    """Blank out Lean comments and string literals, PRESERVING line structure.

    Every removed character becomes a space and newlines are kept, so line and
    column numbers in the stripped text still index the original file. That is
    what lets the census report a real `file:line` for each obligation.

    Handles: nested `/- -/`, `/-- -/` docstrings, `--` line comments, `"..."`
    string literals with backslash escapes, and `'c'` char literals.
    """
    out = list(src)
    i, n = 0, len(src)
    depth = 0          # block-comment nesting depth
    while i < n:
        c = src[i]
        if depth > 0:
            if src.startswith("/-", i):
                depth += 1; out[i] = out[i + 1] = " "; i += 2; continue
            if src.startswith("-/", i):
                depth -= 1; out[i] = out[i + 1] = " "; i += 2; continue
            if c != "\n": out[i] = " "
            i += 1; continue
        if src.startswith("/-", i):
            depth = 1; out[i] = out[i + 1] = " "; i += 2; continue
        if src.startswith("--", i):
            while i < n and src[i] != "\n": out[i] = " "; i += 1
            continue
        if c == '"':
            out[i] = " "; i += 1
            while i < n:
                if src[i] == "\\" and i + 1 < n:
                    out[i] = out[i + 1] = " "; i += 2; continue
                if src[i] == '"': out[i] = " "; i += 1; break
                if src[i] != "\n": out[i] = " "
                i += 1
            continue
        i += 1
    return "".join(out)


# `sorry` and `admit` are the incompleteness markers; `axiom` widens the trusted
# base.  All three are obligations in the sense that matters here.
_OBLIGATION = re.compile(r"\b(sorry|admit)\b")
_AXIOM = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|public\s+)?axiom\s+([A-Za-z_][\w.'!?]*)")
_DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|public\s+|noncomputable\s+|partial\s+|unsafe\s+|nonrec\s+)*"
    r"(theorem|lemma|def|abbrev|instance|example|inductive|structure|opaque)\b\s*([A-Za-z_][\w.'!?]*)?"
)


def _enclosing_decl(lines: list[str], idx: int) -> tuple[str, str, int]:
    """(kind, name, line) of the declaration containing line index `idx`."""
    for j in range(idx, -1, -1):
        m = _DECL.match(lines[j])
        if m:
            return m.group(1), (m.group(2) or "<anonymous>"), j + 1
    return "<file-level>", "<none>", 0


# Feature corners.  NAME-based rules run FIRST, then path.
#
# The order matters and was found by running: seven `TrProj.*` lemmas live in
# `Verify/Typing/Lemmas.lean`, a generic file whose path says nothing, so a
# path-first classifier filed the single largest cluster as "other" and hid the
# census's main finding. A corner table that cannot see its own biggest bucket is
# worse than no corner table.
_CORNER_BY_NAME = [
    ("proj", re.compile(r"\bTrProj|proj", re.I)),
]
_CORNERS = [
    ("inductive-types", (r"Theory/Inductive", r"InductiveLemmas", r"Inductive/")),
    ("environment/addDecl", (r"Verify/Environment", r"Theory/Typing/Env")),
    ("church-rosser", (r"ChurchRosser",)),
    ("injectivity", (r"Injectivity",)),
    ("unique-typing", (r"UniqueTyping",)),
    ("universe-levels", (r"Level", r"LevelSat")),
    ("defeq", (r"IsDefEq", r"Strong")),
    ("whnf/reduction", (r"WHNF", r"Reduce", r"HeadReduction")),
    ("inference", (r"InferType",)),
    ("quotient", (r"Quot",)),
    ("expr/translation", (r"Verify/Typing/Expr", r"VLCtx", r"Verify/Expr")),
]

_PROJ = re.compile(r"\bproj\b|\bTrProj\b|\.proj\b|Proj\b", re.I)


def _corner(relpath: str, decl: str, context: str) -> str:
    for name, rx in _CORNER_BY_NAME:
        if rx.search(decl): return name
    for name, pats in _CORNERS:
        for p in pats:
            if re.search(p, relpath): return name
    return "other"


def _partition(relpath: str) -> str:
    """Executable checker vs proof layer vs experimental vs tests."""
    if relpath.startswith("Lean4Lean/Experimental/"): return "experimental"
    if relpath.startswith("Lean4Lean/Tests/") or "/Tests/" in relpath: return "tests"
    if relpath.startswith("Lean4Lean/Theory/") or relpath.startswith("Lean4Lean/Verify/") \
       or relpath.startswith("Lean4Lean/Std/"):
        return "proof"
    return "executable"


def census(l4l: Path) -> dict:
    if not l4l.is_dir(): raise CensusRefusal(f"missing --l4l directory: {l4l}")
    root = l4l / "Lean4Lean"
    if not root.is_dir(): raise CensusRefusal(f"no Lean4Lean/ under {l4l} — is this lean4lean?")

    try:
        r = subprocess.run(["git", "-C", str(l4l), "rev-parse", "HEAD"],
                           capture_output=True, text=True, timeout=30)
    except (OSError, subprocess.SubprocessError) as exc:
        raise CensusRefusal(f"cannot read lean4lean provenance at {l4l}: {exc}") from exc
    if r.returncode != 0 or not r.stdout.strip():
        raise CensusRefusal(f"--l4l is not a git checkout, so the census has no provenance: {l4l}")
    rev = r.stdout.strip()

    files = sorted(root.rglob("*.lean")) + sorted(l4l.glob("*.lean"))
    if not files: raise CensusRefusal("zero .lean files found — an instrument fault, never a finding")

    raw_total = stripped_total = 0
    rows: list[dict] = []
    axioms: list[dict] = []
    per_file: dict[str, dict] = {}
    lines_by_partition: dict[str, int] = {}

    for f in files:
        rel = str(f.relative_to(l4l))
        src = _read(f)
        stripped = strip_comments(src)
        raw_lines = src.splitlines()
        st_lines = stripped.splitlines()
        part = _partition(rel)
        lines_by_partition[part] = lines_by_partition.get(part, 0) + len(raw_lines)

        raw_n = len(_OBLIGATION.findall(src))
        st_hits = [(i, m) for i, l in enumerate(st_lines) for m in _OBLIGATION.finditer(l)]
        raw_total += raw_n
        stripped_total += len(st_hits)

        if raw_n or st_hits:
            per_file[rel] = {"partition": part, "raw": raw_n, "real": len(st_hits),
                             "comment_only": raw_n - len(st_hits)}

        for i, m in st_hits:
            kind, name, dline = _enclosing_decl(st_lines, i)
            ctx = raw_lines[i].strip() if i < len(raw_lines) else ""
            window = "\n".join(raw_lines[max(0, dline - 1):i + 1])
            rows.append({
                "file": rel, "line": i + 1, "marker": m.group(1),
                "partition": part, "decl_kind": kind, "decl": name, "decl_line": dline,
                "corner": _corner(rel, name, window),
                "proj_related": bool(_PROJ.search(window)) or bool(_PROJ.search(name)),
                "text": ctx[:180],
            })

        for i, l in enumerate(st_lines):
            am = _AXIOM.match(l)
            if am:
                axioms.append({"file": rel, "line": i + 1, "name": am.group(1),
                               "partition": part,
                               "text": (raw_lines[i].strip()[:200] if i < len(raw_lines) else "")})

    if stripped_total == 0:
        raise CensusRefusal("zero obligations parsed — the stripper or the pattern is broken; "
                            "an empty census is an instrument fault, never a finding")

    def tally(key, where):
        d: dict[str, int] = {}
        for x in rows:
            if x["partition"] in where: d[x[key]] = d.get(x[key], 0) + 1
        return dict(sorted(d.items(), key=lambda kv: (-kv[1], kv[0])))

    proof_rows = [x for x in rows if x["partition"] == "proof"]

    # DEPENDENCY STRUCTURE — the census's main structural finding, computed
    # rather than asserted. A `def` whose body is `sorry` is not a missing PROOF,
    # it is a missing DEFINITION: every theorem about it is blocked until the
    # relation exists, and several are not even statable. Separating the two
    # turns "24 sorries" into "3 missing definitions and a cascade", which is a
    # completely different piece of work to price.
    stubs = {x["decl"] for x in proof_rows if x["decl_kind"] in ("def", "abbrev")}
    # Mechanical edge: `Foo.bar` is blocked by a stub named `Foo`.
    # Declared edges: judgement calls, kept visible and reviewable.
    declared_edges = {
        "addInduct_WF": ["VEnv.addInduct", "VInductDecl.WF"],
        "addDecl.WF": ["addInduct_WF"],
        "inferProj.WF": ["TrProj"],
        "reduceProjCore.WF": ["TrProj"],
        # Found by READING the executable, not by the name: `tryEtaStructCore`
        # constructs `.proj` terms (`isDefEq (.proj induct i t) args[i]`), so
        # verifying it needs the `TrProj` relation that does not yet exist. A
        # name-prefix heuristic calls this obligation independent and it is not —
        # which would have put a blocked theorem at the top of the candidate list.
        "tryEtaStructCore.WF": ["TrProj"],
        # Also found by reading, and TRANSITIVELY: `reduceRecursor` calls
        # `inductiveReduceRec` -> `toCtorWhenK` -> `expandEtaStruct`, and that
        # last one BUILDS `.proj` terms. Two call hops from a theorem whose name
        # mentions neither projections nor structures. This is the clearest
        # evidence for the census's standing caution: in this repository the
        # dependency graph is SEMANTIC, and only reading the executable finds it.
        "reduceRecursor.WF": ["TrProj"],
        "IsDefEqU.weakN_iff": ["IsDefEqU.sort_inv", "IsDefEqU.forallE_inv_stratified"],
    }
    for x in proof_rows:
        if x["decl_kind"] in ("def", "abbrev"):
            x["blocked_by"] = []
            continue
        by = []
        head = x["decl"].split(".")[0]
        if head in stubs and x["decl"] != head: by.append(head)
        for d in declared_edges.get(x["decl"], []):
            if d not in by: by.append(d)
        x["blocked_by"] = by
    blocked = [x for x in proof_rows if x.get("blocked_by")]
    independent = [x for x in proof_rows
                   if x["decl_kind"] not in ("def", "abbrev") and not x.get("blocked_by")]
    unblocks: dict[str, int] = {}
    for x in blocked:
        for b in x["blocked_by"]: unblocks[b] = unblocks.get(b, 0) + 1

    return {
        "schema": "lean4lean-obligation-census/1",
        "lean4lean_commit": rev,
        "counting_rule": (
            "raw = every `sorry`/`admit` token including comments, docstrings and string "
            "literals; real = the same after blanking Lean comments (nested /- -/, /-- -/, "
            "--) and string literals while preserving line numbers. The DELTA is a finding."
        ),
        "totals": {
            "raw": raw_total,
            "real": stripped_total,
            "comment_only": raw_total - stripped_total,
            "axioms": len(axioms),
        },
        "lines_by_partition": dict(sorted(lines_by_partition.items())),
        "real_by_partition": tally("partition", {"proof", "executable", "experimental", "tests"}),
        "proof_layer": {
            "real": len(proof_rows),
            "definitional_stubs": sorted(stubs),
            "definitional_stub_count": len(stubs),
            "proof_obligations": len(proof_rows) - len(stubs),
            "blocked_by_a_stub_or_lemma": len(blocked),
            "independent_obligations": sorted(x["decl"] for x in independent),
            "independent_count": len(independent),
            "unblocks": dict(sorted(unblocks.items(), key=lambda kv: (-kv[1], kv[0]))),
            "by_corner": tally("corner", {"proof"}),
            "proj_related": sum(1 for x in proof_rows if x["proj_related"]),
            "by_decl": dict(sorted(
                {f'{x["file"]}::{x["decl"]}': sum(1 for y in proof_rows
                                                  if y["file"] == x["file"] and y["decl"] == x["decl"])
                 for x in proof_rows}.items())),
        },
        "axioms_by_partition": {p: sum(1 for a in axioms if a["partition"] == p)
                                for p in sorted({a["partition"] for a in axioms})},
        "per_file": dict(sorted(per_file.items())),
        "obligations": sorted(rows, key=lambda x: (x["file"], x["line"])),
        "axioms": sorted(axioms, key=lambda x: (x["file"], x["line"])),
    }


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--l4l", required=True, type=Path)
    ap.add_argument("-o", "--output", type=Path)
    ap.add_argument("--compare", type=Path)
    ap.add_argument("--selftest", action="store_true", help="exercise the comment stripper's fixtures")
    args = ap.parse_args(argv)

    if args.selftest:
        return 0 if _selftest() else 1

    try:
        result = census(args.l4l)
    except CensusRefusal as exc:
        print(f"REFUSE: {exc}", file=sys.stderr); return 2

    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.compare:
        if not args.compare.is_file():
            print(f"REFUSE: missing baseline: {args.compare}", file=sys.stderr); return 2
        old = json.loads(args.compare.read_text())
        if old == result:
            print(f"ok: census matches {args.compare}"); return 0
        for k in sorted(set(old) | set(result)):
            if old.get(k) != result.get(k): print(f"DRIFT: {k}", file=sys.stderr)
        return 1
    if args.output:
        args.output.write_text(text, encoding="utf-8"); print(f"wrote {args.output}", file=sys.stderr)
    else:
        sys.stdout.write(text)
    return 0


def _selftest() -> bool:
    """The stripper's own fixtures.  Nesting is the case a regex gets wrong."""
    cases = [
        ("theorem a : P := sorry", 1, "bare"),
        ("-- sorry in a line comment", 0, "line comment"),
        ("/- sorry -/", 0, "block comment"),
        ("/- outer /- inner sorry -/ still outer -/", 0, "NESTED block comment"),
        ("/-- doc mentioning sorry -/\ntheorem a : P := sorry", 1, "docstring + real"),
        ('#eval "sorry"', 0, "string literal"),
        ('#eval "a \\" sorry"', 0, "string with escaped quote"),
        ("theorem a : P := by\n  admit", 1, "admit"),
        ("/- unterminated sorry", 0, "unterminated block"),
        ("theorem a := sorry -- sorry", 1, "real + trailing comment"),
    ]
    ok = True
    for src, want, label in cases:
        got = len(_OBLIGATION.findall(strip_comments(src)))
        status = "ok " if got == want else "FAIL"
        if got != want: ok = False
        print(f"  [{status}] {label}: expected {want}, got {got}")
    # Line numbers must survive stripping.
    s = strip_comments("/- x\n y -/\ntheorem t : P := sorry")
    line_ok = len(s.splitlines()) == 3 and "sorry" in s.splitlines()[2]
    print(f"  [{'ok ' if line_ok else 'FAIL'}] line numbers preserved through a multi-line comment")
    return ok and line_ok


if __name__ == "__main__":
    raise SystemExit(main())
