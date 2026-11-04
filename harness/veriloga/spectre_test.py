#!/usr/bin/env python3
"""Validate the imported Verilog-A resistor against Cadence Spectre.

Spectre is an independent floating-point oracle. It is never a theorem
dependency; the Lean proof is over the OpenVAF AST projection and relational
contribution semantics.
"""

from __future__ import annotations

from pathlib import Path
import re
import shutil
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[2]
MODEL = ROOT / "Examples/verilog-a/resistor/resistor.va"
VECTORS = (1.0, 2.5, 5.0)


def parse_nutascii(path: Path) -> dict[str, float]:
    text = path.read_text()
    header, values_text = text.split("Values:", maxsplit=1)
    variables = re.search(
        r"No\. Variables:\s*(\d+).*?Variables:(.*)",
        header,
        re.DOTALL,
    )
    if variables is None:
        raise RuntimeError("Spectre output has no variable table")
    count = int(variables.group(1))
    names = [
        fields[1].lower()
        for line in variables.group(2).splitlines()
        if len(fields := line.split()) >= 2 and fields[0].isdigit()
    ]
    if len(names) != count:
        raise RuntimeError("Spectre variable table is truncated")
    tokens = values_text.split()
    if len(tokens) != count + 1 or int(tokens[0]) != 0:
        raise RuntimeError("expected exactly one Spectre operating point")
    return dict(zip(names, map(float, tokens[1:])))


def deck(directory: Path) -> Path:
    instances = []
    saves = []
    for index, voltage in enumerate(VECTORS):
        instances.extend(
            [
                f"Vdrive{index} (p{index} 0) vsource dc={voltage}",
                f"Rmodel{index} (p{index} 0) resistor",
            ]
        )
        saves.extend((f"p{index}", f"Vdrive{index}:p"))
    path = directory / "resistor_veriloga.scs"
    path.write_text(
        "\n".join(
            [
                "simulator lang=spectre",
                "global 0",
                f'ahdl_include "{MODEL}"',
                *instances,
                "dcop dc write=\"spectre.dc\"",
                "save " + " ".join(saves),
                "",
            ]
        )
    )
    return path


def main() -> int:
    executable = shutil.which("spectre")
    if executable is None:
        raise SystemExit("spectre not found on PATH")
    failures = 0
    with tempfile.TemporaryDirectory(prefix="leanmodels-veriloga-") as tmp:
        directory = Path(tmp)
        source = deck(directory)
        raw = directory / "resistor.raw"
        run = subprocess.run(
            [
                executable,
                "-log",
                "-format",
                "nutascii",
                "-raw",
                str(raw),
                "-outdir",
                str(directory),
                str(source),
            ],
            cwd=ROOT,
            capture_output=True,
            text=True,
            timeout=120,
        )
        if run.returncode != 0:
            raise RuntimeError(
                f"Spectre failed:\n{run.stdout}\n{run.stderr}"
            )
        values = parse_nutascii(raw)

    print(f"{'voltage':>10} {'Lean law':>16} {'Spectre current':>18}  verdict")
    print("-" * 62)
    for index, voltage in enumerate(VECTORS):
        expected = -voltage / 1000.0
        key = f"vdrive{index}:p"
        observed = values[key]
        ok = abs(observed - expected) <= 1e-9
        failures += not ok
        print(
            f"{voltage:10.6g} {expected:16.9g} "
            f"{observed:18.9g}  {'MATCH' if ok else 'MISMATCH'}"
        )
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
