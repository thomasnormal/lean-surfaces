#!/usr/bin/env python3
"""Regression tests for C++ differential verdict provenance."""

import importlib.util
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("cpp_diff_test", ROOT / "harness" / "cpp_diff_test.py")
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


def main():
    fixture = {"id": "fixture", "corpus": "fixture", "kind": "callable",
               "rung": 3, "expect": "match"}
    rows = module.differential([fixture], {"fixture": "ok 7"}, {"fixture": ("NATIVE", "7")})
    assert rows[0]["verdict"] == "WITNESS"
    print("cpp differential reporting: ok")


if __name__ == "__main__":
    main()
