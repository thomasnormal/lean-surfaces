#!/usr/bin/env python3
"""Differential row for C effective-type pointer punning."""

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
    with tempfile.TemporaryDirectory(prefix="c-effective-type-diff-") as temp:
        source = Path(temp) / "pun.c"
        source.write_text("int main(void) { int i = 0x12345678; return *(short *)&i; }\n")
        native = Path(temp) / "pun"
        compiled = run([clang, "--no-default-config", "-std=c23", "-O0",
                        str(source), "-o", str(native)])
        if compiled.returncode:
            raise RuntimeError("native compile failed: " + compiled.stderr)
        envelope = Path(temp) / "pun.json"
        extracted = run([sys.executable, "extractors/c/extract.py", str(source), "-o", str(envelope)])
        if extracted.returncode:
            raise RuntimeError("extraction failed: " + extracted.stderr)
        model = run(["lake", "env", "lean", "-j", "1", "--run",
                     "harness/c_filler_runner.lean", str(envelope)])
        if model.returncode != 3 or "effective types" not in model.stderr:
            raise RuntimeError("expected loud effective-type refusal, got %r %r" %
                               (model.stdout, model.stderr))
        print("pointer-pun: REFUSE (native exit %s)" % run([str(native)]).returncode)
    return 0


if __name__ == "__main__":
    sys.exit(main())
