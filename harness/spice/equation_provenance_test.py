#!/usr/bin/env python3
"""Check that equation provenance rejects transitive specification leakage."""

from __future__ import annotations

import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
BAD = ROOT / "harness" / "spice" / "equation_provenance_bad.lean"


def main() -> int:
    run = subprocess.run(
        ["lake", "env", "lean", str(BAD)],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    output = run.stdout
    if run.returncode == 0:
        raise SystemExit(
            "equation provenance adversary unexpectedly compiled successfully"
        )
    required = (
        "Equation dependency guard for "
        "LeanModels.Circuit.EquationProvenanceAdversarial.physicalProgram",
        "#equation_guard: "
        "`LeanModels.Circuit.EquationProvenanceAdversarial.bakedProgram` "
        "transitively depends on a forbidden specification declaration",
    )
    missing = [text for text in required if text not in output]
    if missing:
        raise SystemExit(
            "equation provenance adversary failed for the wrong reason; "
            f"missing diagnostics: {missing}\n{output}"
        )
    print("equation-provenance: clean program accepted; baked program rejected")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
