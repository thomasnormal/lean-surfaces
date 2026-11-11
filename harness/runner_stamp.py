#!/usr/bin/env python3
"""Fail closed when the runner lacks a current Lean-source stamp."""

import importlib.machinery
import importlib.util
import os
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
loader = importlib.machinery.SourceFileLoader("leanpy_stamp", str(ROOT / "tools" / "leanpy"))
spec = importlib.util.spec_from_loader("leanpy_stamp", loader)
leanpy = importlib.util.module_from_spec(spec)
spec.loader.exec_module(leanpy)


def main():
    runner = leanpy.runner_command(build=False, strict=True)
    if runner is None:
        raise SystemExit(3)
    print("runner_stamp: verified " + os.path.basename(runner[0]))


if __name__ == "__main__":
    main()
