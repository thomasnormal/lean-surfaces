#!/usr/bin/env python3
"""The Lean tier's SPEC-RULE census (family-architecture.md §5.4, §5.5).

Builds the spec-mirror index for `docs/lean-tier-charter.md`: the inference
rules of Carneiro's *The Type Theory of Lean*, counted from the LaTeX source and
attributed to a judgment family and a section number.

WHY THIS INSTRUMENT IS AWKWARD, stated up front because it shapes every design
choice below: **this spec is not machine-readable.** Unlike WebAssembly — whose
SpecTec emits named rules, so a mirror can be checked by set equality — this
document typesets its rules as bare `\\frac{premises}{conclusion}` inside display
math. There is no `\\inferrule`, no `mathpar`, no rule macro, and **the rules
have no names**. Only five carry an inline tag: (beta), (eta), (zeta), (delta),
(iota).

So the unit of measure is: a `\\frac`/`\\dfrac` occurrence, attributed to the
most recent `\\boxed{...}` judgment declaration and the current section. That is
a real measurement and it is reproducible, but it is a proxy for "a rule" rather
than the thing itself, and §"KNOWN UNDERCOUNTS" below says exactly where the
proxy fails. A charter that quoted this number without that caveat would be
overclaiming.

PIN: the thesis has TWO HEADS. The published v1.0 PDF is NOT an ancestor of
`master`, and `master` carries a correction to the inductive constructor level
constraint that the PDF does not. This instrument REFUSES to run against
anything but the pinned `master` commit unless `--allow-unpinned` is passed.

Usage:
    lean_spec_census.py --tex DIR [-o OUT]
    lean_spec_census.py --tex DIR --compare docs/lean-spec-census.json
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

# The commit this tier cites against.  See `docs/lean-tier-charter.md` §7.2.
PINNED_COMMIT = "0ba178704380d2fad751f020d461b293f47e36d5"


class CensusRefusal(Exception):
    """The instrument declines, loudly.  An input fault, never a finding."""


def _read(path: Path) -> str:
    if not path.is_file():
        raise CensusRefusal(f"missing input: {path}")
    return path.read_text(encoding="utf-8", errors="replace")


# --------------------------------------------------------------------------

_INPUT = re.compile(r"^\s*\\(?:input|include)\{([^}]+)\}", re.M)
_SECTION = re.compile(r"\\(sub)*section\*?\{")
_BOXED = re.compile(r"\\boxed\{((?:[^{}]|\{[^{}]*\})*)\}")
_RULE = re.compile(r"\\d?frac\b")
# An inline rule tag such as `(\beta)\ \frac{...}` — the only names the source has.
_TAG = re.compile(r"\((\\[a-zA-Z]+)\)\s*\\?\s*\\d?frac")
# An explicit elision standing for unwritten congruence/compatibility rules.
_ELISION = re.compile(r"\\c?dots|\\ldots|\.\.\.")


def _strip_comments(text: str) -> str:
    """Drop LaTeX line comments, honoring `\\%`."""
    out = []
    for line in text.splitlines():
        i, esc = 0, False
        cut = len(line)
        while i < len(line):
            c = line[i]
            if esc: esc = False
            elif c == "\\": esc = True
            elif c == "%": cut = i; break
            i += 1
        out.append(line[:cut])
    return "\n".join(out)


def _brace_body(text: str, open_idx: int) -> tuple[str, int]:
    """Body of a balanced `{...}` starting at `open_idx` (which indexes the `{`)."""
    depth, i = 0, open_idx
    while i < len(text):
        if text[i] == "{": depth += 1
        elif text[i] == "}":
            depth -= 1
            if depth == 0: return text[open_idx + 1 : i], i + 1
        i += 1
    raise CensusRefusal("unbalanced braces in source")


def _section_title(text: str, m: re.Match) -> tuple[int, str]:
    """(depth, title) for a `\\section`/`\\subsection`/`\\subsubsection` match."""
    depth = len(re.findall(r"sub", m.group(0)))
    body, _ = _brace_body(text, m.end() - 1)
    return depth, body.strip()


def _file_order(tex_dir: Path) -> list[str]:
    """Document order from main.tex's \\input list — NOT alphabetical.

    Section numbers depend on it, so a glob would silently produce wrong
    citations.
    """
    main = _read(tex_dir / "main.tex")
    names = _INPUT.findall(_strip_comments(main))
    if not names:
        raise CensusRefusal("main.tex declares no \\input files — cannot establish section order")
    return names


def _census_files(tex_dir: Path) -> dict:
    order = _file_order(tex_dir)
    counters = [0, 0, 0]  # section, subsection, subsubsection
    families: dict[str, dict] = {}
    current: str | None = None
    per_file: dict[str, dict] = {}
    sections: list[dict] = []
    total_rules = 0

    for name in order:
        path = tex_dir / f"{name}.tex"
        if not path.is_file():
            raise CensusRefusal(f"main.tex inputs {name!r} but {path} is missing")
        text = _strip_comments(_read(path))
        file_rules = 0
        # A judgment family does not carry across a file boundary.
        current = None

        # Walk the file in ONE pass so that sections, boxed judgments and rules
        # interleave in true source order — the attribution depends on it.
        events = []
        for m in _SECTION.finditer(text): events.append((m.start(), "sec", m))
        for m in _BOXED.finditer(text): events.append((m.start(), "box", m))
        for m in _RULE.finditer(text): events.append((m.start(), "rule", m))
        events.sort(key=lambda e: e[0])

        for pos, kind, m in events:
            if kind == "sec":
                depth, title = _section_title(text, m)
                counters[depth] += 1
                for d in range(depth + 1, 3): counters[d] = 0
                num = ".".join(str(c) for c in counters[: depth + 1] if True)
                num = ".".join(str(counters[d]) for d in range(depth + 1))
                sections.append({"number": num, "title": title, "file": name})
            elif kind == "box":
                current = m.group(1).strip()
                families.setdefault(
                    current,
                    {"judgment": current, "file": name, "declared_at_section": _cur_num(counters),
                     "rules": 0, "tags": [], "elided": False},
                )
            else:
                total_rules += 1
                file_rules += 1
                if current is None:
                    # A rule outside any boxed judgment: real, and worth seeing.
                    current = f"(untagged in {name})"
                    families.setdefault(
                        current,
                        {"judgment": current, "file": name, "declared_at_section": _cur_num(counters),
                         "rules": 0, "tags": [], "elided": False},
                    )
                families[current]["rules"] += 1

        # Tags and elisions are attributed per family by locality.
        for tm in _TAG.finditer(text):
            fam = _nearest_family(families, text, tm.start(), name)
            if fam and tm.group(1) not in families[fam]["tags"]:
                families[fam]["tags"].append(tm.group(1))
        for em in _ELISION.finditer(text):
            fam = _nearest_family(families, text, em.start(), name)
            if fam: families[fam]["elided"] = True

        per_file[name] = {"rules": file_rules, "lines": len(text.splitlines())}

    for f in families.values(): f["tags"].sort()
    return {
        "file_order": order,
        "per_file": per_file,
        "sections": sections,
        "families": families,
        "total_typeset_rules": total_rules,
    }


def _cur_num(counters: list[int]) -> str:
    parts = [c for c in counters if c]
    return ".".join(str(c) for c in counters[: len(parts)]) if parts else "0"


def _nearest_family(families: dict, text: str, pos: int, fname: str) -> str | None:
    """The boxed judgment most recently declared before `pos` in this file."""
    best, best_pos = None, -1
    for m in _BOXED.finditer(text[:pos]):
        if m.start() > best_pos: best, best_pos = m.group(1).strip(), m.start()
    if best and best in families and families[best]["file"] == fname: return best
    return None


def _pin_check(tex_dir: Path, allow_unpinned: bool) -> str:
    try:
        out = subprocess.run(["git", "-C", str(tex_dir), "rev-parse", "HEAD"],
                             capture_output=True, text=True, timeout=30)
    except (OSError, subprocess.SubprocessError) as exc:
        raise CensusRefusal(f"cannot read spec checkout at {tex_dir}: {exc}") from exc
    if out.returncode != 0:
        raise CensusRefusal(f"not a git checkout: {tex_dir}")
    head = out.stdout.strip()
    if head != PINNED_COMMIT and not allow_unpinned:
        raise CensusRefusal(
            f"spec checkout is at {head[:12]}, not the pinned {PINNED_COMMIT[:12]}. "
            "The thesis has TWO HEADS and the published PDF carries a rule its author "
            "has since corrected; cite the pin or pass --allow-unpinned deliberately."
        )
    return head


def census(tex_dir: Path, allow_unpinned: bool = False) -> dict:
    if not tex_dir.is_dir(): raise CensusRefusal(f"missing --tex directory: {tex_dir}")
    head = _pin_check(tex_dir, allow_unpinned)
    raw = _census_files(tex_dir)

    if raw["total_typeset_rules"] < 100:
        raise CensusRefusal(
            f"implausible parse: {raw['total_typeset_rules']} rules (expected >100) — "
            "the source's rule macro may have changed"
        )
    if not raw["families"]:
        raise CensusRefusal("zero judgment families parsed — an instrument fault, never a finding")

    # KERNEL-RELEVANT = declared in the axioms chapter.  That chapter IS the
    # kernel's specification; everything after it is metatheory or model
    # construction, which a checker does not implement.
    kernel_file = "axioms"
    fams = raw["families"]
    kernel = {k: v for k, v in fams.items() if v["file"] == kernel_file}
    kernel_rules = sum(v["rules"] for v in kernel.values())

    by_file: dict[str, int] = {}
    for v in fams.values(): by_file[v["file"]] = by_file.get(v["file"], 0) + v["rules"]

    return {
        "schema": "lean-spec-census/1",
        "source": "digama0/lean-type-theory (LaTeX source of Carneiro, The Type Theory of Lean)",
        "commit": head,
        "pinned": head == PINNED_COMMIT,
        "licence": "NO LICENSE FILE IN-TREE — cite by section and rule, never vendor",
        "method": (
            "counts \\frac/\\dfrac occurrences attributed to the most recent \\boxed{} "
            "judgment and the current section. The source has NO rule macro and NO rule "
            "names; this is a reproducible proxy, not a named-rule set equality."
        ),
        "known_undercounts": [
            "align*-typeset computation rules (the iota menagerie, the quotient lift rule) "
            "are NOT \\frac and are NOT counted here",
            "families flagged `elided` end in an explicit ... standing for an unwritten set "
            "of congruence/compatibility rules described only in prose",
        ],
        "file_order": raw["file_order"],
        "per_file_rules": by_file,
        "per_file_lines": {k: v["lines"] for k, v in raw["per_file"].items()},
        "total_typeset_rules": raw["total_typeset_rules"],
        "kernel_relevant": {
            "chapter_file": kernel_file,
            "families": len(kernel),
            "rules": kernel_rules,
            "elided_families": sorted(k for k, v in kernel.items() if v["elided"]),
        },
        "families": [fams[k] for k in sorted(fams)],
        "sections": raw["sections"],
        "named_rules": sorted({t for v in fams.values() for t in v["tags"]}),
    }


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--tex", required=True, type=Path, help="the lean-type-theory checkout")
    ap.add_argument("-o", "--output", type=Path)
    ap.add_argument("--compare", type=Path)
    ap.add_argument("--allow-unpinned", action="store_true",
                    help="run against a commit other than the cited pin (deliberate override)")
    args = ap.parse_args(argv)

    try:
        result = census(args.tex, args.allow_unpinned)
    except CensusRefusal as exc:
        print(f"REFUSE: {exc}", file=sys.stderr)
        return 2

    text = json.dumps(result, indent=2, sort_keys=True) + "\n"

    if args.compare:
        if not args.compare.is_file():
            print(f"REFUSE: missing baseline: {args.compare}", file=sys.stderr)
            return 2
        old = json.loads(args.compare.read_text())
        if old == result:
            print(f"ok: census matches {args.compare}")
            return 0
        for key in sorted(set(old) | set(result)):
            if old.get(key) != result.get(key): print(f"DRIFT: {key}", file=sys.stderr)
        return 1

    if args.output:
        args.output.write_text(text, encoding="utf-8")
        print(f"wrote {args.output}", file=sys.stderr)
    else:
        sys.stdout.write(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
