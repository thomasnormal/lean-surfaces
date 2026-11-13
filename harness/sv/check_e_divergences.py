#!/usr/bin/env python3
"""Re-run the three historical E/simulator divergence rows.

The rows are intentionally explicit: ``dyn32`` may report the registered
Xcelium partial-overhang departure, while the two typed-generate rows must be
ordinary E matches.  A new disagreement or refusal fails this gate.
"""

from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
CASES = ("dyn32", "fold_cgrow_n33", "fold_cgrow_n40")
PASS = re.compile(r"^(\S+)\s+PASS\s+\[(.*)\]", re.MULTILINE)


def run(case):
    return subprocess.run(
        [sys.executable, "harness/sv/diff_test2.py", "--backend", "e0",
         "--sim", "iverilog", "--no-xcheck", "--case", case],
        cwd=ROOT, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, timeout=120, check=False,
        start_new_session=True).stdout


def main():
    for case in CASES:
        print(f"running {case}", flush=True)
        output = run(case)
        match = PASS.search(output)
        if match is None or match.group(1) != case:
            raise SystemExit(f"{case}: expected PASS, got:\n{output}")
        if "fold_cgrow" in case and "declared" in match.group(2).lower():
            raise SystemExit(f"{case}: unexpected declared departure:\n{output}")
        print(f"{case}: PASS ({match.group(2)})")
    print("three historical E divergence rows triaged: 2 MATCH, 1 declared simulator departure")


if __name__ == "__main__":
    main()
