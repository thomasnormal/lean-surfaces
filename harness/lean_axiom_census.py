#!/usr/bin/env python3
"""The Lean tier's AXIOM-DEPENDENCY census (M1 inch 5).

Drives `harness/lean_axiom_deps.lean` over a module set and reports **which
declarations depend on a native computation, and which one**.

WHAT THIS IS FOR. `docs/family-architecture.md` §0.1 II(a) — Thomas's graded
decide ladder — requires any rung-3 (`native_decide` / `bv_decide`) use to carry
its `#print axioms` receipt at the use site, because *"the trust boundary is
per-theorem and visible, never ambient."* This computes that receipt for a whole
module set instead of one constant at a time, so the property can be GATED
rather than reviewed.

The three trust extensions it looks for were measured, not recalled
(`docs/lean-kernel-census.json`): `Lean.ofReduceBool`, `Lean.ofReduceNat`,
`Lean.trustCompiler` — all three deprecated upstream since 2026-02-01. `sorryAx`
is tracked SEPARATELY: an incomplete proof and a compiler-trusting proof are
different failures and pooling them would misreport both.

It runs ONE small `lean` process on a dependency-free file, niced, so it needs
no `lake` and no build lock (BUILD_LOCK_PROTOCOL rule 3).

Usage:
    lean_axiom_census.py --modules Init.Core Init.Prelude [-o OUT]
    lean_axiom_census.py --modules ... --lean-path DIR[:DIR] --compare docs/....json
    lean_axiom_census.py --modules ... --gate      # exit 1 if anything is native-dependent
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
SCRIPT = HERE / "lean_axiom_deps.lean"
DEFAULT_TOOLCHAIN = Path.home() / ".elan/toolchains/leanprover--lean4---v4.33.0-rc1"


class CensusRefusal(Exception):
    """The instrument declines, loudly.  An input fault, never a finding."""


def run(modules: list[str], toolchain: Path, lean_path: str | None, timeout: int) -> dict:
    if not modules: raise CensusRefusal("no modules given")
    if not SCRIPT.is_file(): raise CensusRefusal(f"missing instrument: {SCRIPT}")
    lean = toolchain / "bin" / "lean"
    if not lean.is_file(): raise CensusRefusal(f"no lean binary at {lean}")

    env = dict(os.environ)
    if lean_path:
        for part in lean_path.split(":"):
            if part and not Path(part).is_dir():
                raise CensusRefusal(f"--lean-path entry is not a directory: {part}")
        env["LEAN_PATH"] = lean_path + ":" + env.get("LEAN_PATH", "")

    # nice -n 19 and a single small process: BUILD_LOCK_PROTOCOL rule 3.
    cmd = ["nice", "-n", "19", str(lean), "--run", str(SCRIPT), *modules]
    try:
        out = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout, env=env)
    except subprocess.TimeoutExpired as exc:
        raise CensusRefusal(f"lean run exceeded {timeout}s on {modules}") from exc
    if out.returncode != 0:
        err = (out.stderr or out.stdout).strip().splitlines()
        raise CensusRefusal(f"lean run failed (exit {out.returncode}): {err[0] if err else '(no output)'}")
    try:
        data = json.loads(out.stdout)
    except json.JSONDecodeError as exc:
        raise CensusRefusal(f"instrument did not emit JSON: {exc}") from exc

    if data.get("scanned", 0) == 0:
        # A zero-row scan is an INSTRUMENT fault, never a finding (§5.4).
        raise CensusRefusal(
            f"zero declarations scanned for {modules} — the module names are probably wrong "
            "or unreachable on LEAN_PATH; an empty census is never a result"
        )

    rows = data.get("rows", [])
    native = [r for r in rows if r.get("native")]
    sorried = [r for r in rows if r.get("sorry")]
    by_axiom: dict[str, int] = {}
    for r in native:
        for a in r["native"]: by_axiom[a] = by_axiom.get(a, 0) + 1

    return {
        "schema": "lean-axiom-census/1",
        "toolchain": toolchain.name,
        "modules": sorted(data["modules"]),
        "scanned": data["scanned"],
        "internal_skipped": data["internal_skipped"],
        "native_dependent": len(native),
        "sorry_dependent": len(sorried),
        "native_by_axiom": dict(sorted(by_axiom.items())),
        "native_rows": sorted(native, key=lambda r: r["decl"]),
        "sorry_rows": sorted([r["decl"] for r in sorried]),
    }


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--modules", nargs="+", required=True)
    ap.add_argument("--toolchain", type=Path, default=DEFAULT_TOOLCHAIN)
    ap.add_argument("--lean-path", help="colon-separated dirs prepended to LEAN_PATH")
    ap.add_argument("--timeout", type=int, default=900)
    ap.add_argument("-o", "--output", type=Path)
    ap.add_argument("--compare", type=Path)
    ap.add_argument("--gate", action="store_true",
                    help="exit 1 if any declaration depends on a native computation or a sorry")
    args = ap.parse_args(argv)

    try:
        result = run(args.modules, args.toolchain, args.lean_path, args.timeout)
    except CensusRefusal as exc:
        print(f"REFUSE: {exc}", file=sys.stderr)
        return 2

    text = json.dumps(result, indent=2, sort_keys=True) + "\n"

    if args.compare:
        if not args.compare.is_file():
            print(f"REFUSE: missing baseline: {args.compare}", file=sys.stderr); return 2
        old = json.loads(args.compare.read_text())
        if old == result:
            print(f"ok: census matches {args.compare}"); return 0
        for key in sorted(set(old) | set(result)):
            if old.get(key) != result.get(key): print(f"DRIFT: {key}", file=sys.stderr)
        return 1

    if args.output:
        args.output.write_text(text, encoding="utf-8"); print(f"wrote {args.output}", file=sys.stderr)
    else:
        sys.stdout.write(text)

    if args.gate and (result["native_dependent"] or result["sorry_dependent"]):
        print(f"GATE FAILED: {result['native_dependent']} native-dependent, "
              f"{result['sorry_dependent']} sorry-dependent", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
