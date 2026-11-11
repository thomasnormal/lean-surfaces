#!/usr/bin/env python3
"""Differential refusal rows for unsequenced C side effects."""

import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
CLANG = os.environ.get("LEANC_CLANG", "clang")
ROWS = {
    "binary-write-write": "int main(void) { int i = 0; i++ + i++; return i; }",
    "assignment-write": "int main(void) { int i = 0; i = i++ + 1; return i; }",
    "index-write": "int main(void) { int i = 0; int a[2] = {0, 0}; a[i++] = i++; return a[0]; }",
    "call-write-write": "int f(int a, int b) { return a + b; } int main(void) { int i = 0; return f(i++, i++); }",
    "pure-call": "int f(int a, int b) { return a + b; } int main(void) { return f(1, 2); }",
}


def run(args, **kwargs):
    return subprocess.run(args, cwd=ROOT, text=True, capture_output=True, timeout=120, **kwargs)


def main():
    clang = shutil.which(CLANG)
    if not clang:
        raise RuntimeError("LEANC_CLANG must select Clang 21.1.8")
    first = run([clang, "--version"]).stdout.splitlines()[0]
    if not first.startswith("clang version 21.1.8 "):
        raise RuntimeError("expected Clang 21.1.8, got " + first)
    print("C oracle:", first)
    with tempfile.TemporaryDirectory(prefix="c-order-diff-") as temp:
        work = Path(temp)
        for name, body in ROWS.items():
            source = work / (name + ".c")
            source.write_text(body + "\n")
            native = work / name
            compiled = run([clang, "--no-default-config", "-std=c23", "-O0",
                            str(source), "-o", str(native)])
            if compiled.returncode:
                raise RuntimeError(name + ": native compile failed: " + compiled.stderr)
            envelope = work / (name + ".json")
            extracted = run([sys.executable, "extractors/c/extract.py", str(source), "-o", str(envelope)])
            if extracted.returncode:
                raise RuntimeError(name + ": extraction failed: " + extracted.stderr)
            model = run(["lake", "env", "lean", "-j", "1", "--run",
                         "harness/c_filler_runner.lean", str(envelope)])
            if name == "pure-call":
                native_status = run([str(native)]).returncode
                if model.returncode or model.stdout.strip() != str(native_status):
                    raise RuntimeError(name + ": native=%s model=%r stderr=%r" %
                                       (native_status, model.stdout, model.stderr))
                print(name + ": MATCH " + str(native_status))
            else:
                if model.returncode != 3 or "unsequenced side effects" not in model.stderr:
                    raise RuntimeError(name + ": expected loud refusal, got %r %r" %
                                       (model.stdout, model.stderr))
                print(name + ": REFUSE")
    return 0


if __name__ == "__main__":
    sys.exit(main())
