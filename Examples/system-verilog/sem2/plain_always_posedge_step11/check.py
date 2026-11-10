#!/usr/bin/env python3
"""Compare source-shaped plain-always E traces with both gated simulators."""

import importlib.util
from pathlib import Path

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location(
    "case_check", HERE.parent / "case_always_ff_step11/check.py")
case_check = importlib.util.module_from_spec(spec)
spec.loader.exec_module(case_check)

if __name__ == "__main__":
    case_check.main(HERE, (("plainedge", "plain_always_posedge_step11", 6),
                           ("kinds", "plain_always_kinds_step11", 13)))
