#!/usr/bin/env python3
"""Differential refusal row for goto past a declaration."""

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
    with tempfile.TemporaryDirectory(prefix="c-goto-decl-diff-") as temp:
        source = Path(temp) / "goto.c"
        source.write_text("int main(void) { int x = 1; goto L; int x2 = 2; L: x = 7; return x; }\n")
        native = Path(temp) / "goto"
        compiled = run([clang, "--no-default-config", "-std=c23", "-O0",
                        str(source), "-o", str(native)])
        if compiled.returncode:
            raise RuntimeError("native compile failed: " + compiled.stderr)
        envelope = Path(temp) / "goto.json"
        extracted = run([sys.executable, "extractors/c/extract.py", str(source), "-o", str(envelope)])
        if extracted.returncode:
            raise RuntimeError("extraction failed: " + extracted.stderr)
        model = run(["lake", "env", "lean", "-j", "1", "--run",
                     "harness/c_filler_runner.lean", str(envelope)])
        if model.returncode != 3 or "goto skips" not in model.stderr:
            raise RuntimeError("expected goto declaration refusal, got %r %r" %
                               (model.stdout, model.stderr))
        print("goto-skips-decl: REFUSE")
    return 0


if __name__ == "__main__":
    sys.exit(main())
