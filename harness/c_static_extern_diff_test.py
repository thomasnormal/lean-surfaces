#!/usr/bin/env python3
"""Differential refusal rows for block-scope static and extern objects."""

import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
CLANG = os.environ.get("LEANC_CLANG", "clang")
ROWS = {
    "static-local": "int f(void) { static int n = 0; return ++n; } int main(void) { return f(); }",
    "extern-local": "int g = 3; int main(void) { extern int g; return g; }",
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
    with tempfile.TemporaryDirectory(prefix="c-static-extern-diff-") as temp:
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
            if model.returncode != 3 or "storage class" not in model.stderr:
                raise RuntimeError(name + ": expected storage refusal, got %r %r" %
                                   (model.stdout, model.stderr))
            print(name + ": REFUSE storage-class")
    return 0


if __name__ == "__main__":
    sys.exit(main())
