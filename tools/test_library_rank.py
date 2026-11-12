#!/usr/bin/env python3
"""Regression tests for the PY-REAL wall ranking instrument."""

import json
import subprocess
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
SCRIPT = ROOT / "harness" / "library_rank.py"


def main():
    subprocess.run([sys.executable, str(SCRIPT), "--self-test"], check=True, cwd=ROOT)
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory) / "rows.json"
        path.write_text(json.dumps({
            "rows": [
                {"module": "one", "file": "one.py", "provenance": "test",
                 "observed_wall": "import", "census_walls": ["import"],
                 "nfunctions": 2, "ncalls": 3, "nmatched": 3, "verdict": "REFUSED",
                 "oracle": {"functions": [{"name": "f"}, {"name": "g"}]},
                 "calls": [{"function": "f", "verdict": "MATCH",
                            "cpython": {"status": "ok"}}]},
                {"module": "two", "file": "two.py", "provenance": "test",
                 "observed_wall": "class-creation", "census_walls": ["class-creation"],
                 "nfunctions": 1, "ncalls": 1},
                {"module": "three", "file": "three.py", "provenance": "test",
                 "observed_wall": "import", "census_walls": ["import"],
                 "verdict": "PARTIAL", "nfunctions": 1, "ncalls": 1,
                 "nmatched": 1,
                 "oracle": {"functions": [{"name": "h"}]},
                 "calls": [{"function": "h", "verdict": "MATCH",
                            "cpython": {"status": "ok"}}]},
            ]
        }), encoding="utf-8")
        ranked = Path(directory) / "rank.json"
        subprocess.run([sys.executable, str(SCRIPT), "--json", str(ranked), str(path)],
                       check=True, cwd=ROOT, stdout=subprocess.DEVNULL)
        result = json.loads(ranked.read_text(encoding="utf-8"))
        assert result["rows"] == 3
        assert [item["wall"] for item in result["ranking"]] == ["import", "class-creation"]
        assert result["ranking"][0]["sole"] == 2
        by_wall = {item["wall"]: item for item in result["ranking"]}
        assert by_wall["import"]["potential_verified_rows"] == 1
        assert by_wall["import"]["potential_verified_functions"] == 1
        assert by_wall["import"]["verified_functions"] == 2
        assert json.loads(ranked.read_text(encoding="utf-8"))["function_totals"]["verified_functions"] == 2
        filtered = Path(directory) / "filtered.json"
        subprocess.run([sys.executable, str(SCRIPT), "--provenance", "test",
                        "--json", str(filtered), str(path)],
                       check=True, cwd=ROOT, stdout=subprocess.DEVNULL)
        assert json.loads(filtered.read_text(encoding="utf-8"))["rows"] == 3
    print("test_library_rank: 2 tests passed")


if __name__ == "__main__":
    main()
