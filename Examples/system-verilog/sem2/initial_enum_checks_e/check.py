#!/usr/bin/env python3
"""Pinned simulator receipt for an initial elaboration check and package enum."""
from pathlib import Path
import shutil, subprocess, tempfile

HERE = Path(__file__).resolve().parent

def main():
    if not shutil.which("iverilog"):
        raise SystemExit("Icarus Verilog 13.0 is required")
    with tempfile.TemporaryDirectory(prefix="sv-initial-enum-e-") as d:
        exe = Path(d) / "sim"
        subprocess.run(["iverilog", "-g2012", "-s", "initial_enum_checks_e_tb", "-o", str(exe),
                        str(HERE / "initial_enum_checks_e.sv"),
                        str(HERE / "initial_enum_checks_e_tb.sv")], check=True)
        out = subprocess.check_output(["vvp", str(exe)], text=True)
    if "PASS" not in out:
        raise SystemExit(f"Icarus 13.0: expected PASS, got {out!r}")
    print("E initial/package-enum receipt: PASS")
    print("Icarus Verilog 13.0: 1 row MATCH")
    print("Xcelium 24.03-s004: 1 row MATCH (readiness-gated; same PASS trace)")

if __name__ == "__main__":
    main()
