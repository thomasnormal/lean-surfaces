#!/usr/bin/env python3
"""Smoke concrete statement domains against CPython and both interpreters.

The target list names representative ``#py_check`` statements from the
curated proof examples. Their argument domains come from the structured
`harness/cases.json` rows; no Lean or Python source text is reparsed here.
"""

import json
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
CASES = ROOT / "harness" / "cases.json"
TARGETS = (
    ("Examples/python/tri/tri.py", "tri"),
    ("Examples/python/tut_01/tut_01.py", "double"),
    ("Examples/python/tut_02/tut_02.py", "square"),
    ("Examples/python/tut_03/tut_03.py", "relu"),
    ("Examples/python/tut_04/tut_04.py", "fact"),
    ("Examples/python/tut_05/tut_05.py", "pymod"),
    ("Examples/python/tut_06/tut_06.py", "true_div"),
    ("Examples/python/with_lab/with_lab.py", "bound_value"),
    ("Examples/python/walrus_lab/walrus_lab.py", "w_basic"),
    ("Examples/python/cls_lab/cls_lab.py", "make_get"),
    ("Examples/python/float_lab/float_lab.py", "tenth"),
    ("Examples/python/bench_bisect/bench_bisect.py", "bisect_left"),
)


def smoke_cases():
    cases = json.loads(CASES.read_text(encoding="utf-8"))
    out = []
    for file_name, function in TARGETS:
        matches = [case for case in cases
                   if case["file"] == file_name and case["function"] == function]
        if not matches:
            raise SystemExit("statement_smoke: missing structured row for %s::%s" %
                             (file_name, function))
        case = dict(matches[0])
        case["expect"] = "match"
        case["note"] = "statement smoke domain sampled from the proof example"
        out.append(case)
    return out


def main():
    path = ROOT / "harness" / ".statement_smoke_cases.json"
    path.write_text(json.dumps(smoke_cases(), indent=2) + "\n", encoding="utf-8")
    try:
        for proof in (False, True):
            command = [sys.executable, str(ROOT / "harness" / "diff_test.py"),
                       "--cases", str(path), "--no-build", "--runner",
                       str(ROOT / ".lake" / "build" / "bin" / "leanmodels-run")]
            if proof:
                command.append("--proof-interpreter")
            if subprocess.call(command, cwd=str(ROOT)):
                return 1
    finally:
        path.unlink(missing_ok=True)
    print("statement_smoke: %d structured proof-example statements checked in both modes" %
          len(TARGETS))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
