#!/usr/bin/env python3
"""The Lean tier's SPEC-MIRROR CORRESPONDENCE manifest (family-architecture.md §5.5).

Answers, mechanically and with a drift guard: **for each judgment family the
thesis specifies, what in `lean4lean/Lean4Lean/Theory/` realizes it, and how do
the counts compare?**

This is §5.5's coverage-by-clause manifest with the clause replaced by the rule.
Nobody in the field has one: the correspondence between Carneiro's thesis and
Carneiro's formalization is, today, a human judgement recorded nowhere.

WHAT IS MECHANICAL AND WHAT IS DECLARED — the honest split, because a manifest
that blurred it would be the very drift it exists to catch:

* **MECHANICAL** — the constructor lists of `Theory/`'s inductives, and the rule
  counts from `docs/lean-spec-census.json`. Both are re-derived on every run and
  a change in either is DRIFT.
* **DECLARED** — the MAP from a thesis judgment to a `Theory/` inductive. That
  is this tier's editorial contribution, it cites a thesis section per row, and
  it lives in `MAP` below where a reviewer can argue with it. The instrument
  REFUSES if a declared target has vanished, so the map cannot rot silently.

Coverage is deliberately NOT reported as a percentage. The two sides do not
stand in a 1:1 relation — see `STRUCTURAL` — and a percentage would imply they
do, which is exactly the overclaim §5.5 exists to prevent.

Usage:
    lean_rule_correspondence.py --l4l DIR --spec-census docs/lean-spec-census.json [-o OUT]
    lean_rule_correspondence.py --l4l DIR --spec-census ... --compare docs/lean-rule-correspondence.json
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


# --------------------------------------------------------------------------
# THE DECLARED MAP.  One row per thesis judgment family (the `judgment` key is
# the LaTeX exactly as `lean_spec_census.py` emits it, so the two files join).
# --------------------------------------------------------------------------

MAP = [
    {
        "judgment": r"\Gamma\vdash e:\alpha",
        "name": "Typing",
        "thesis_section": "2.1",
        "targets": ["IsDefEq"],
        "relation": "FUSED",
        "note": "Typing is not a separate judgment in Theory/. `HasType` is DEFINED as the "
                "diagonal of IsDefEq (`IsDefEq env U Γ e e A`, Typing/Basic.lean), so the "
                "thesis's typing and defeq rules share one inductive.",
    },
    {
        "judgment": r"\Gamma\vdash e\equiv e'",
        "name": "Definitional equality",
        "thesis_section": "2.2",
        "targets": ["IsDefEq"],
        "relation": "FUSED",
        "note": "Same inductive as Typing; see that row.",
    },
    {
        "judgment": r"\Gamma\vdash\alpha\type",
        "name": "Is-a-type",
        "thesis_section": "2.1",
        "targets": [],
        "relation": "DEFINED-NOT-INDUCTIVE",
        "note": "`IsType` is a def (`∃ u, HasType Γ A (.sort u)`), not an inductive. The "
                "thesis's single rule is the definition, so there is nothing to count.",
    },
    {
        "judgment": r"\vdash\Gamma\ok",
        "name": "Context well-formedness",
        "thesis_section": "2.1",
        "targets": ["Ctx.LiftN", "Lookup"],
        "relation": "RESHAPED",
        "note": "Theory/ carries no `⊢ Γ ok` judgment. Contexts are `List VExpr` and their "
                "discipline is carried by `Lookup` plus the lifting/instantiation family, "
                "so the thesis's 2 rules have no direct counterpart.",
    },
    {
        "judgment": r"\ell\equiv\ell'",
        "name": "Level equality",
        "thesis_section": "2.2",
        "targets": ["VLevel"],
        "relation": "SEMANTIC",
        "note": "Theory/ defines level equivalence SEMANTICALLY (`≈` via evaluation into ℕ "
                "under all substitutions) rather than by the thesis's algorithmic rules. "
                "This is a deliberate and documented divergence, not a gap.",
    },
    {
        "judgment": r"\ell\le \ell'+n",
        "name": "Level order",
        "thesis_section": "2.2",
        "targets": ["VLevel"],
        "relation": "SEMANTIC",
        "note": "The thesis's 14 algorithmic inequality rules are replaced by the semantic "
                "order. The 14 rules are what an IMPLEMENTATION needs; Theory/ specifies "
                "the relation they are meant to decide.",
    },
    {
        "judgment": r"\Gamma\vdash e\Leftrightarrow e'",
        "name": "Algorithmic defeq",
        "thesis_section": "2.3",
        "targets": ["IsDefEqStrong"],
        "relation": "PARTIAL",
        "note": "The thesis's algorithmic judgment is the checker's spec. Theory/'s nearest "
                "artifact is `IsDefEqStrong` (Typing/Strong.lean); the executable checker's "
                "correctness is stated in Verify/, against IsDefEq rather than against a "
                "mirrored algorithmic judgment.",
    },
    {
        "judgment": r"e\rightsquigarrow e'",
        "name": "Head reduction",
        "thesis_section": "2.3",
        "targets": ["WHRed", "StRed"],
        "relation": "RESHAPED",
        "note": "Theory/Typing/HeadReduction.lean carries WHRed and StRed. The thesis family "
                "is ELIDED in the source (ends in `...`), so a faithful mirror must "
                "reconstruct the missing congruence rules from prose before comparing.",
    },
    {
        "judgment": r"\Gamma;t:F\vdash K\spec",
        "name": "Inductive specification",
        "thesis_section": "2.6.1",
        "targets": ["VInductDecl"],
        "relation": "STUB",
        "note": "THE SEAM. `Theory/Inductive.lean` is 8 lines: `VInductDecl.WF` and "
                "`VEnv.addInduct` are both `sorry`. The abstract specification of inductive "
                "types has not been written.",
    },
    {
        "judgment": r"\Gamma;t:F\vdash \alpha\ctor",
        "name": "Constructor",
        "thesis_section": "2.6.1",
        "targets": ["VInductDecl"],
        "relation": "STUB",
        "note": "Same stub; and the thesis family is ELIDED besides.",
    },
    {
        "judgment": r"\Gamma;t:F\vdash K\LE",
        "name": "Large elimination",
        "thesis_section": "2.6.2",
        "targets": ["VInductDecl"],
        "relation": "STUB",
        "note": "Same stub.",
    },
    {
        "judgment": r"\Gamma;t:F\vdash \alpha\LEctor",
        "name": "Subsingleton constructor",
        "thesis_section": "2.6.2",
        "targets": ["VInductDecl"],
        "relation": "STUB",
        "note": "Same stub.",
    },
]

# Structural facts about the two artifacts that no per-family row can express.
STRUCTURAL = [
    {
        "id": "typing-defeq-fusion",
        "what": "The thesis states typing and definitional equality as two judgments; "
                "Theory/ fuses them into one inductive `IsDefEq Γ e e' A`, with typing "
                "recovered as the diagonal `HasType Γ e A := IsDefEq Γ e e A`.",
        "consequence": "Per-family rule counts CANNOT be compared 1:1. This is the single "
                       "biggest reason coverage is not a percentage here.",
    },
    {
        "id": "environment-carried-defeqs",
        "what": "`IsDefEq.extra` admits any equation the ENVIRONMENT declares (`env.defeqs`). "
                "Delta reduction and the iota/quotient computation rules enter the theory as "
                "environment data rather than as inference rules.",
        "consequence": "Thesis rules for delta/iota/quot have no constructor to match. They "
                       "are discharged when a declaration is ADMITTED, not when a term is checked.",
    },
    {
        "id": "levels-semantic-not-algorithmic",
        "what": "The thesis gives 15 algorithmic level rules (equality + order); Theory/ "
                "defines the relation semantically by evaluation into ℕ.",
        "consequence": "21% of the thesis's kernel-relevant rules describe an ALGORITHM whose "
                       "specification in Theory/ is a different kind of object. Mirroring them "
                       "means proving the algorithm decides the semantic relation.",
    },
    {
        "id": "proj-absent",
        "what": "`VExpr` has 6 constructors; Lean's `Expr` has 12. `proj` has no abstract "
                "counterpart at all, and the thesis's grammar does not contain it either.",
        "consequence": "The tier's hard center: unspecified in the thesis AND unmodelled in "
                       "Theory/, while being kernel-primitive and the site of four live "
                       "soundness bugs.",
    },
]

_IND = re.compile(r"^inductive\s+([A-Za-z_][\w.']*)\b")
_CTOR = re.compile(r"^\s{2}\|\s*([a-zA-Z_][\w']*)")


def _read(p: Path) -> str:
    if not p.is_file(): raise CensusRefusal(f"missing input: {p}")
    return p.read_text(encoding="utf-8", errors="replace")


def _inductives(theory: Path) -> dict[str, dict]:
    """Every `inductive` under Theory/, with its constructors, in declaration order."""
    found: dict[str, dict] = {}
    for path in sorted(theory.rglob("*.lean")):
        text = _read(path)
        lines = text.splitlines()
        i = 0
        while i < len(lines):
            m = _IND.match(lines[i])
            if not m:
                i += 1; continue
            name = m.group(1)
            ctors, depth, j = [], 0, i + 1
            while j < len(lines):
                line = lines[j]
                s = line.strip()
                if s.startswith("deriving") or (line and not line[0].isspace() and s):
                    break
                depth += line.count("/-") - line.count("-/")
                if depth <= 0:
                    cm = _CTOR.match(line)
                    if cm: ctors.append(cm.group(1))
                j += 1
            # A name may be declared once per file; keep the first and record the file.
            found.setdefault(name, {
                "name": name,
                "file": str(path.relative_to(theory.parent.parent)),
                "line": i + 1,
                "constructors": ctors,
                "n": len(ctors),
            })
            i = j
    return found


def _sorry_stubs(theory: Path) -> dict:
    """The inductive-specification stub, measured rather than asserted."""
    p = theory / "Inductive.lean"
    text = _read(p)
    body = [l for l in text.splitlines() if l.strip()]
    sorries = [l.strip() for l in body if re.search(r"\bsorry\b", l)]
    return {"file": "Lean4Lean/Theory/Inductive.lean", "total_lines": len(text.splitlines()),
            "nonblank_lines": len(body), "sorry_lines": sorries}


def _l4l_rev(l4l: Path) -> str:
    try:
        out = subprocess.run(["git", "-C", str(l4l), "rev-parse", "HEAD"],
                             capture_output=True, text=True, timeout=30)
    except (OSError, subprocess.SubprocessError) as exc:
        raise CensusRefusal(f"cannot read lean4lean checkout at {l4l}: {exc}") from exc
    if out.returncode != 0: raise CensusRefusal(f"not a git checkout: {l4l}")
    return out.stdout.strip()


def census(l4l: Path, spec_census: Path) -> dict:
    if not l4l.is_dir(): raise CensusRefusal(f"missing --l4l directory: {l4l}")
    theory = l4l / "Lean4Lean" / "Theory"
    if not theory.is_dir(): raise CensusRefusal(f"no Theory/ under {l4l} — is this lean4lean?")

    spec = json.loads(_read(spec_census))
    if spec.get("schema") != "lean-spec-census/1":
        raise CensusRefusal(f"--spec-census is not a lean-spec-census/1 document: {spec_census}")
    if not spec.get("pinned"):
        raise CensusRefusal("the spec census was taken at an unpinned commit; refusing to build a "
                            "correspondence against a citation base that is not the cited one")

    by_judgment = {f["judgment"]: f for f in spec["families"]}
    inds = _inductives(theory)

    rows, missing = [], []
    for entry in MAP:
        fam = by_judgment.get(entry["judgment"])
        if fam is None:
            raise CensusRefusal(
                f"declared map row {entry['name']!r} names judgment {entry['judgment']!r}, "
                "which the spec census does not contain — the map has drifted from the spec"
            )
        tgts = []
        for t in entry["targets"]:
            if t in inds:
                tgts.append({"inductive": t, "constructors": inds[t]["n"],
                             "file": inds[t]["file"], "names": inds[t]["constructors"]})
            elif t == "VInductDecl":
                tgts.append({"inductive": t, "constructors": 0, "file": "Lean4Lean/Theory/Inductive.lean",
                             "names": [], "note": "stub — see inductive_stub"})
            else:
                missing.append({"row": entry["name"], "target": t})
        rows.append({
            "name": entry["name"], "judgment": entry["judgment"],
            "thesis_section": entry["thesis_section"], "thesis_rules": fam["rules"],
            "thesis_elided": fam["elided"], "relation": entry["relation"],
            "targets": tgts, "note": entry["note"],
        })

    if missing:
        raise CensusRefusal(
            "declared map targets no longer exist in Theory/: "
            + ", ".join(f"{m['row']}→{m['target']}" for m in missing)
            + ". The map must be re-reviewed, not silently repaired."
        )

    mapped = sum(r["thesis_rules"] for r in rows)
    kernel_total = spec["kernel_relevant"]["rules"]
    if mapped != kernel_total:
        raise CensusRefusal(
            f"the map covers {mapped} thesis rules but the spec census counts {kernel_total} "
            "kernel-relevant. Every kernel-relevant family must appear in MAP exactly once."
        )

    by_rel: dict[str, int] = {}
    for r in rows: by_rel[r["relation"]] = by_rel.get(r["relation"], 0) + r["thesis_rules"]

    return {
        "schema": "lean-rule-correspondence/1",
        "lean4lean_commit": _l4l_rev(l4l),
        "spec_commit": spec["commit"],
        "method": (
            "MECHANICAL: Theory/ inductive constructor lists, and rule counts joined from "
            "lean-spec-census.json. DECLARED: the judgment→inductive map in MAP, one cited "
            "row per family, which the instrument refuses to let rot."
        ),
        "coverage_is_not_a_percentage": (
            "The two artifacts are not in a 1:1 relation — typing and defeq are fused, delta/"
            "iota/quot enter as environment data, and the level rules are replaced by a "
            "semantic order. A percentage would assert a correspondence that does not exist."
        ),
        "thesis_kernel_rules": kernel_total,
        "rules_by_relation": dict(sorted(by_rel.items())),
        "theory_inductives_total": len(inds),
        "isDefEq_constructors": inds.get("IsDefEq", {}).get("n"),
        "vexpr_constructors": inds.get("VExpr", {}).get("n"),
        "inductive_stub": _sorry_stubs(theory),
        "rows": rows,
        "structural_divergences": STRUCTURAL,
    }


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--l4l", required=True, type=Path, help="a lean4lean checkout")
    ap.add_argument("--spec-census", required=True, type=Path, help="docs/lean-spec-census.json")
    ap.add_argument("-o", "--output", type=Path)
    ap.add_argument("--compare", type=Path)
    args = ap.parse_args(argv)

    try:
        result = census(args.l4l, args.spec_census)
    except CensusRefusal as exc:
        print(f"REFUSE: {exc}", file=sys.stderr)
        return 2

    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.compare:
        if not args.compare.is_file():
            print(f"REFUSE: missing baseline: {args.compare}", file=sys.stderr); return 2
        old = json.loads(args.compare.read_text())
        if old == result:
            print(f"ok: correspondence matches {args.compare}"); return 0
        for key in sorted(set(old) | set(result)):
            if old.get(key) != result.get(key): print(f"DRIFT: {key}", file=sys.stderr)
        return 1
    if args.output:
        args.output.write_text(text, encoding="utf-8"); print(f"wrote {args.output}", file=sys.stderr)
    else:
        sys.stdout.write(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
