#!/usr/bin/env python3
"""Refuse a call whose Clang DeclRefExpr resolves to a local variable."""

import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
CLANG = os.environ.get("LEANC_CLANG", "clang")


def run(args):
    return subprocess.run(args, cwd=ROOT, text=True, capture_output=True, timeout=120)


def main():
    clang = shutil.which(CLANG)
    if not clang:
        raise RuntimeError("LEANC_CLANG must select Clang 21.1.8")
    first = run([clang, "--version"]).stdout.splitlines()[0]
    if not first.startswith("clang version 21.1.8 "):
        raise RuntimeError("expected Clang 21.1.8, got " + first)
    print("C oracle:", first)
    source_text = """int target(void) { return 1; }
int main(void) { int (*target)(void) = 0; return target(); }
"""
    with tempfile.TemporaryDirectory(prefix="c-name-resolution-") as temp:
        work = Path(temp)
        source = work / "shadow.c"
        source.write_text(source_text)
        native = work / "shadow"
        compiled = run([clang, "--no-default-config", "-std=c23", "-O0",
                        str(source), "-o", str(native)])
        if compiled.returncode:
            raise RuntimeError("native compile failed: " + compiled.stderr)
        envelope = work / "shadow.json"
        extracted = run([sys.executable, "extractors/c/extract.py", str(source), "-o", str(envelope)])
        if extracted.returncode:
            raise RuntimeError("extraction failed: " + extracted.stderr)
        manifest = work / "manifest.json"
        manifest.write_text(json.dumps({
            "tests": [{"name": "local-callee", "status": "parsed",
                       "envelope": str(envelope), "why": ""}]
        }))
        model = run(["lake", "exe", "c-torture-run", str(manifest)])
        if model.returncode or "local-callee\trefused-unsupported\t" not in model.stdout:
            raise RuntimeError("expected resolved-local-callee refusal, got %r %r" %
                               (model.stdout, model.stderr))
        print("local-variable-callee: REFUSE (identity guard; layout may refuse first)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
