#!/usr/bin/env python3
"""The Lean tier's kernel-vocabulary census (family-architecture.md §5.4).

Measures the KERNEL LANGUAGE of Lean 4 at a pinned toolchain: the `Expr` and
`Level` constructors, the declaration kinds, the built-in axioms, the reduction
rules the C++ kernel implements, and the literal-acceleration set.

TWO INPUTS, because the kernel is written in two languages and neither half is
optional:

  --lean-src    the toolchain's shipped Lean sources (`src/lean` under an elan
                toolchain).  Defines the DATATYPES: `Expr`, `Level`,
                `Literal`, `Declaration`, `ConstantInfo`, and the axioms.
  --kernel-src  the lean4 repository's `src/kernel` C++ tree at the SAME tag.
                Defines the RULES: whnf, delta, iota, eta, proof irrelevance,
                quotient reduction, the accelerated `Nat` operations.

The second is NOT shipped inside an elan toolchain (measured: `src/kernel` is
present but empty).  It must be fetched from the lean4 repository at the tag
matching the toolchain, and the instrument REFUSES rather than guessing if the
two disagree about the version.

Out-of-tree corpus, so per §5.4 this is deliberately NOT wired into CI.

Usage:
    lean_kernel_census.py --lean-src DIR --kernel-src DIR [-o OUT]
    lean_kernel_census.py --lean-src DIR --kernel-src DIR --compare docs/lean-kernel-census.json
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

# --------------------------------------------------------------------------
# refusals: every path here is exercised by the instrument's own fixtures.
# --------------------------------------------------------------------------


class CensusRefusal(Exception):
    """The instrument declines, loudly.  Never a finding — always an input fault."""


def _read(path: Path) -> str:
    if not path.is_file():
        raise CensusRefusal(f"missing input: {path}")
    return path.read_text(encoding="utf-8", errors="replace")


def _require_rows(rows: list, what: str, least: int) -> list:
    """A zero-row (or implausibly thin) parse is an INSTRUMENT fault, never a finding."""
    if len(rows) < least:
        raise CensusRefusal(f"implausible parse: {len(rows)} {what} (expected at least {least})")
    return rows


# --------------------------------------------------------------------------
# the DATATYPES, from the shipped Lean sources
# --------------------------------------------------------------------------

# A constructor line inside an `inductive` block: `  | name (field : T) ...`
# or the ascription form `  | name : T -> U`.
_CTOR = re.compile(r"^\s{2}\|\s*([a-zA-Z][A-Za-z0-9_']*)")


def _inductive_ctors(text: str, name: str, *, path: str) -> list[dict]:
    """Constructors of `inductive <name> where`, in DECLARATION ORDER.

    Order is preserved rather than sorted: the kernel's own tag numbering and
    every export format's constructor codes follow it, so alphabetising here
    would destroy the datum a reader needs.
    """
    start = re.search(rf"^inductive {re.escape(name)}\b.*$", text, re.M)
    if not start:
        raise CensusRefusal(f"no `inductive {name}` in {path}")
    lines = text[start.start():].splitlines()
    base = text[: start.start()].count("\n") + 1
    out, depth = [], 0
    for i, line in enumerate(lines[1:], start=1):
        stripped = line.strip()
        # `deriving`, or a new top-level declaration, ends the block.
        if stripped.startswith("deriving") or (line and not line[0].isspace() and i > 1):
            break
        depth += line.count("/-") - line.count("-/")
        if depth > 0:
            continue
        m = _CTOR.match(line)
        if m:
            out.append({"name": m.group(1), "line": base + i, "text": stripped})
    return out


_AXIOM = re.compile(r"^(?:protected\s+)?axiom\s+([A-Za-z_][\w.']*)\s*(.*)$")


def _axioms(lean_src: Path) -> list[dict]:
    """Real `axiom` declarations under Init/ — docstring examples excluded.

    The exclusion is load-bearing and was found by measurement: a naive grep over
    the toolchain reports five extra `axiom` lines, and ALL FIVE sit inside
    ```-fenced code blocks in docstrings (`Init/Grind/Attr.lean`,
    `Init/Grind/Tactics.lean`, and two under `Lean/`).  Counting them would
    overstate Lean's trusted base by more than double.
    """
    rows = []
    for path in sorted(lean_src.glob("Init/**/*.lean")):
        text = _read(path)
        in_doc = False
        in_fence = False
        # `Quot.sound` is declared as bare `sound` inside `namespace Quot`, so a
        # census that skipped this would name the single most-cited axiom in Lean
        # wrongly.  Tracked as a stack; `end <name>` and bare `end` both pop.
        ns: list[str] = []
        for n, line in enumerate(text.splitlines(), start=1):
            stripped = line.strip()
            if stripped.startswith("/--"):
                in_doc = not stripped.endswith("-/") or stripped == "/--"
            elif in_doc and stripped.endswith("-/"):
                in_doc = False
            if stripped.startswith("```"):
                in_fence = not in_fence
            if in_doc or in_fence:
                continue
            if m := re.match(r"^namespace\s+([\w.']+)", stripped):
                ns.append(m.group(1))
                continue
            if re.match(r"^end\b", stripped):
                if ns: ns.pop()
                continue
            m = _AXIOM.match(line)
            if m:
                local = m.group(1)
                rows.append(
                    {
                        "name": ".".join(ns + [local]) if ns else local,
                        "local_name": local,
                        "namespace": ".".join(ns),
                        "file": str(path.relative_to(lean_src)),
                        "line": n,
                        "signature": stripped,
                    }
                )
    return rows


# --------------------------------------------------------------------------
# the RULES, from the C++ kernel
# --------------------------------------------------------------------------

# Each reduction rule the kernel implements is a NAMED function, which is why
# this census is a set equality and not a judgement call.  The table below maps
# the family's rule vocabulary onto the kernel's own symbols; the instrument
# then CONFIRMS each symbol exists rather than asserting it does.
_RULES = [
    ("beta", "type_checker.cpp", r"whnf_core", "application of a lambda, inside whnf_core's App case"),
    ("zeta", "type_checker.cpp", r"whnf_core", "let-expansion, inside whnf_core's Let case"),
    ("zeta-fvar", "type_checker.cpp", r"whnf_fvar", "expansion of a let-bound free variable"),
    ("delta", "type_checker.cpp", r"unfold_definition", "definitional unfolding"),
    ("delta-lazy", "type_checker.cpp", r"lazy_delta_reduction", "the defeq loop's lazy unfolding strategy"),
    ("iota", "type_checker.cpp", r"reduce_recursor", "recursor application to a constructor"),
    ("proj", "type_checker.cpp", r"reduce_proj", "structure projection of a constructor"),
    ("eta", "type_checker.cpp", r"try_eta_expansion_core", "function eta"),
    ("eta-struct", "type_checker.cpp", r"try_eta_struct_core", "structure eta"),
    ("proof-irrelevance", "type_checker.cpp", r"is_def_eq_proof_irrel", "any two proofs of a Prop are equal"),
    ("unit-like", "type_checker.cpp", r"is_def_eq_unit_like", "eta for unit-like inductive types"),
    ("nat-lit", "type_checker.cpp", r"reduce_nat", "GMP-backed Nat literal arithmetic"),
    ("nat-pow", "type_checker.cpp", r"reduce_pow", "Nat.pow, guarded separately against blowup"),
    ("string-lit", "type_checker.cpp", r"try_string_lit_expansion", "String literal vs String.mk expansion"),
    ("offset", "type_checker.cpp", r"is_def_eq_offset", "the Nat-offset fast path (n+k vs m+k)"),
    ("quot", "quot.cpp", r"environment::add_quot", "Quot.lift / Quot.ind computation"),
]

# `if (f == *g_nat_<op>) return reduce_bin_nat_(op|pred)(...)` and the succ case.
_NAT_OP = re.compile(r"f == \*g_nat_(\w+)")


def _kernel_rules(kernel_src: Path) -> tuple[list[dict], list[str]]:
    cache: dict[str, str] = {}
    rows = []
    for rule, fname, symbol, note in _RULES:
        text = cache.setdefault(fname, _read(kernel_src / fname))
        hits = [n for n, line in enumerate(text.splitlines(), start=1) if symbol in line]
        if not hits:
            raise CensusRefusal(f"rule {rule!r}: symbol {symbol!r} not found in {fname} — the kernel moved")
        rows.append({"rule": rule, "file": fname, "symbol": symbol, "definition_line": hits[0], "note": note})
    tc = cache["type_checker.cpp"]
    body = tc[tc.index("optional<expr> type_checker::reduce_nat") :]
    body = body[: body.index("\n}\n")]
    nat_ops = sorted(set(_NAT_OP.findall(body)))
    return rows, nat_ops


_KERNEL_EXC = re.compile(r"^class\s+(\w+)\s*:\s*public\s+(\w+)")


def _kernel_exceptions(kernel_src: Path) -> list[dict]:
    """The kernel's own rejection vocabulary — the tier's REFUSE/DIVERGE input."""
    text = _read(kernel_src / "kernel_exception.h")
    rows = [
        {"name": m.group(1), "base": m.group(2), "line": n}
        for n, line in enumerate(text.splitlines(), start=1)
        if (m := _KERNEL_EXC.match(line))
    ]
    return rows


# --------------------------------------------------------------------------
# version agreement
# --------------------------------------------------------------------------


def _toolchain_version(lean_src: Path) -> str:
    """`src/lean` sits two levels under the toolchain root."""
    root = lean_src.parent.parent
    for name in ("lean-toolchain",):
        p = root / name
        if p.is_file():
            return p.read_text().strip()
    # elan names the directory after the toolchain.
    m = re.search(r"---(v[\d.]+(?:-\w+)?)$", root.name)
    if m:
        return f"leanprover/lean4:{m.group(1)}"
    raise CensusRefusal(f"cannot determine toolchain version from {root}")


def _kernel_version(kernel_src: Path) -> str:
    """The kernel checkout's tag, from git.  REFUSES if it is not a checkout."""
    import subprocess

    repo = kernel_src.parent.parent
    try:
        out = subprocess.run(
            ["git", "-C", str(repo), "describe", "--tags", "--exact-match"],
            capture_output=True, text=True, timeout=30,
        )
        if out.returncode == 0:
            return out.stdout.strip()
        out = subprocess.run(
            ["git", "-C", str(repo), "rev-parse", "HEAD"],
            capture_output=True, text=True, timeout=30,
        )
        if out.returncode == 0:
            return out.stdout.strip()[:12]
    except (OSError, subprocess.SubprocessError) as exc:
        raise CensusRefusal(f"cannot read kernel checkout version at {repo}: {exc}") from exc
    raise CensusRefusal(f"not a git checkout: {repo}")


# --------------------------------------------------------------------------


def census(lean_src: Path, kernel_src: Path) -> dict:
    if not lean_src.is_dir(): raise CensusRefusal(f"missing --lean-src directory: {lean_src}")
    if not kernel_src.is_dir(): raise CensusRefusal(f"missing --kernel-src directory: {kernel_src}")

    toolchain = _toolchain_version(lean_src)
    kernel_tag = _kernel_version(kernel_src)
    # The two halves must be the same release, or the census is measuring a chimera.
    short = toolchain.split(":")[-1]
    if short not in kernel_tag and kernel_tag not in short:
        raise CensusRefusal(
            f"version mismatch: toolchain is {toolchain!r} but kernel checkout is {kernel_tag!r}. "
            "The datatypes and the rules must come from the SAME tag."
        )

    expr_text = _read(lean_src / "Lean/Expr.lean")
    level_text = _read(lean_src / "Lean/Level.lean")
    decl_text = _read(lean_src / "Lean/Declaration.lean")

    expr = _require_rows(_inductive_ctors(expr_text, "Expr", path="Lean/Expr.lean"), "Expr constructors", 10)
    level = _require_rows(_inductive_ctors(level_text, "Level", path="Lean/Level.lean"), "Level constructors", 5)
    lit = _require_rows(_inductive_ctors(expr_text, "Literal", path="Lean/Expr.lean"), "Literal constructors", 2)
    decl = _require_rows(_inductive_ctors(decl_text, "Declaration", path="Lean/Declaration.lean"), "Declaration kinds", 6)
    cinfo = _require_rows(_inductive_ctors(decl_text, "ConstantInfo", path="Lean/Declaration.lean"), "ConstantInfo kinds", 7)

    # Elaboration-only constructors: the kernel rejects declarations containing
    # them (Lean/Environment.lean, `Environment`'s own docstring).  This split is
    # the tier's actual vocabulary — a Lean surface never has to model `mvar`.
    elab_only_expr = {"mvar", "fvar"}
    elab_only_level = {"mvar"}

    axioms = _require_rows(_axioms(lean_src), "axioms", 5)
    # The trust extensions underwrite `native_decide`; family-architecture §0.1
    # II(a)'s ladder governs exactly these.
    # Matched on the LOCAL name: these live in `namespace Lean`, and a classifier
    # keyed on the bare name would silently mis-file every one of them as sound.
    trust_ext = {"ofReduceBool", "ofReduceNat", "trustCompiler"}
    unsound_marker = {"sorryAx"}
    for a in axioms:
        a["class"] = (
            "trust-extension" if a["local_name"] in trust_ext
            else "unsoundness-marker" if a["local_name"] in unsound_marker
            else "sound"
        )
    if not [a for a in axioms if a["class"] == "trust-extension"]:
        raise CensusRefusal("no trust-extension axioms found — the ofReduceBool family moved or was renamed")

    rules, nat_ops = _kernel_rules(kernel_src)
    excs = _require_rows(_kernel_exceptions(kernel_src), "kernel exceptions", 10)

    cpp = sorted(kernel_src.glob("*.cpp")) + sorted(kernel_src.glob("*.h"))
    kernel_lines = sum(len(_read(p).splitlines()) for p in cpp)

    return {
        "schema": "lean-kernel-census/1",
        "toolchain": toolchain,
        "kernel_checkout": kernel_tag,
        "kernel_cpp": {
            "files": len(cpp),
            "lines": kernel_lines,
            "by_file": {p.name: len(_read(p).splitlines()) for p in cpp},
        },
        "expr": {
            "total": len(expr),
            "kernel_admissible": len([c for c in expr if c["name"] not in elab_only_expr]),
            "elaboration_only": sorted(elab_only_expr),
            "constructors": expr,
        },
        "level": {
            "total": len(level),
            "kernel_admissible": len([c for c in level if c["name"] not in elab_only_level]),
            "elaboration_only": sorted(elab_only_level),
            "constructors": level,
        },
        "literal": {"total": len(lit), "constructors": lit},
        "declaration": {"total": len(decl), "kinds": decl},
        "constant_info": {"total": len(cinfo), "kinds": cinfo},
        "axioms": {
            "total": len(axioms),
            "sound": [a["name"] for a in axioms if a["class"] == "sound"],
            "trust_extensions": [a["name"] for a in axioms if a["class"] == "trust-extension"],
            "unsoundness_markers": [a["name"] for a in axioms if a["class"] == "unsoundness-marker"],
            "rows": axioms,
        },
        "reduction_rules": {"total": len(rules), "rules": rules},
        "nat_acceleration": {"total": len(nat_ops), "ops": nat_ops},
        "kernel_exceptions": {"total": len(excs), "rows": excs},
    }


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--lean-src", required=True, type=Path, help="toolchain src/lean directory")
    ap.add_argument("--kernel-src", required=True, type=Path, help="lean4 src/kernel directory at the SAME tag")
    ap.add_argument("-o", "--output", type=Path, help="write JSON here (default: stdout)")
    ap.add_argument("--compare", type=Path, help="compare against a committed census and exit non-zero on drift")
    args = ap.parse_args(argv)

    try:
        result = census(args.lean_src, args.kernel_src)
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
            if old.get(key) != result.get(key):
                print(f"DRIFT: {key}", file=sys.stderr)
        return 1

    if args.output:
        args.output.write_text(text, encoding="utf-8")
        print(f"wrote {args.output}", file=sys.stderr)
    else:
        sys.stdout.write(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
