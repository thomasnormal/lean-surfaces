#!/usr/bin/env python3
"""Compare E's wildcard-case trace with both gated source simulators."""

import importlib.util
from pathlib import Path

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location(
    "case_check", HERE.parent / "case_always_ff_step11/check.py")
case_check = importlib.util.module_from_spec(spec)
spec.loader.exec_module(case_check)

if __name__ == "__main__":
    case_check.main(HERE, (("wild", "casez_casex_always_ff_step11", 13),))
