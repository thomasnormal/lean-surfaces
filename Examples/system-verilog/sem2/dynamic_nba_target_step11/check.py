#!/usr/bin/env python3
"""Compare loaded-source dynamic NBA execution in E with gated simulators."""
import importlib.util
from pathlib import Path

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location(
    "case_check", HERE.parent / "case_always_ff_step11/check.py")
case_check = importlib.util.module_from_spec(spec)
spec.loader.exec_module(case_check)

if __name__ == "__main__":
    case_check.main(HERE, (("target", "dynamic_nba_target_step11", 7),
                           ("issue", "dynamic_nba_issue_step11", 13)))
