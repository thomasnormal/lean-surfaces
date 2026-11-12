#!/usr/bin/env python3
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent


def main():
    subprocess.run([sys.executable, "tools/check_python_dependents.py", "--self-test"],
                   cwd=ROOT, check=True)
    out = subprocess.check_output([
        sys.executable, "tools/check_python_dependents.py",
        "LeanModels/Python/Semantics.lean"], cwd=ROOT, text=True)
    lines = out.splitlines()
    assert "LeanModels.Python.Obs" in lines
    assert "LeanModels.Python.Surface" in lines
    assert all("LeanModels/Sv" not in line for line in lines)
    assert "LeanModels.Python.Semantics" not in lines
    print("test_python_dependents: 2 cases passed")


if __name__ == "__main__":
    main()
