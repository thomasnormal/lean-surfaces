#!/usr/bin/env python3
"""Differential row for designated union initialization."""

import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
CLANG = os.environ.get("LEANC_CLANG", "clang")


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
    with tempfile.TemporaryDirectory(prefix="c-union-init-diff-") as temp:
        source = Path(temp) / "union.c"
        source.write_text("union U { int i; char c; }; union U u = {.c = 5}; int main(void) { return u.c; }\n")
        native = Path(temp) / "union"
        compiled = run([clang, "--no-default-config", "-std=c23", "-O0",
                        str(source), "-o", str(native)])
        if compiled.returncode:
            raise RuntimeError("native compile failed: " + compiled.stderr)
        envelope = Path(temp) / "union.json"
        extracted = run([sys.executable, "extractors/c/extract.py", str(source), "-o", str(envelope)])
        if extracted.returncode:
            raise RuntimeError("extraction failed: " + extracted.stderr)
        model = run(["lake", "env", "lean", "-j", "1", "--run",
                     "harness/c_filler_runner.lean", str(envelope)])
        native_status = run([str(native)]).returncode
        if model.returncode or model.stdout.strip() != str(native_status):
            raise RuntimeError("native=%s model=%r stderr=%r" %
                               (native_status, model.stdout, model.stderr))
        print("union-designated-member: MATCH " + str(native_status))
    return 0


if __name__ == "__main__":
    sys.exit(main())
