#!/usr/bin/env python3
import json
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent


def main():
    subprocess.run([sys.executable, "tools/python_opaque_imports.py", "--self-test"],
                   cwd=ROOT, check=True)
    table = json.loads((ROOT / "docs/python-opaque-imports.json").read_text())
    assert table["python"].startswith("Python 3.9.")
    rows = table["modules"]
    assert len(rows) == 10 and all(row["eligible"] for row in rows)
    assert len({row["module"] for row in rows}) == len(rows)
    assert all(len(row["sha256"]) == 64 for row in rows)
    print("test_python_opaque_imports: table and self-test passed")


if __name__ == "__main__":
    main()
