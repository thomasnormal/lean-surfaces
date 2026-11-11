#!/usr/bin/env python3
"""Differential refusal row for unspecified adjacent pointer equality."""

import os
import json
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
    with tempfile.TemporaryDirectory(prefix="c-ptr-eq-boundary-") as temp:
        source = Path(temp) / "ptr.c"
        source.write_text("int main(void) { int a[1] = {0}; int b[1] = {0}; return (&a[1] == &b[0]) ? 1 : 0; }\n")
        native = Path(temp) / "ptr"
        compiled = run([clang, "--no-default-config", "-std=c23", "-O0",
                        str(source), "-o", str(native)])
        if compiled.returncode:
            raise RuntimeError("native compile failed: " + compiled.stderr)
        envelope = Path(temp) / "ptr.json"
        extracted = run([sys.executable, "extractors/c/extract.py", str(source), "-o", str(envelope)])
        if extracted.returncode:
            raise RuntimeError("extraction failed: " + extracted.stderr)
        manifest = Path(temp) / "manifest.json"
        manifest.write_text(json.dumps({
            "tests": [{"name": "ptr", "status": "parsed",
                       "envelope": str(envelope), "why": ""}]
        }))
        model = run(["lake", "exe", "c-torture-run", str(manifest)])
        if model.returncode or "ptr\trefused-unsupported\t" not in model.stdout \
                or "unspecified adjacent boundary" not in model.stdout:
            raise RuntimeError("expected boundary refusal, got %r %r" %
                               (model.stdout, model.stderr))
        native_run = run([str(native)])
        print("adjacent-one-past-equality: REFUSE (native exit %s)" % native_run.returncode)
    return 0


if __name__ == "__main__":
    sys.exit(main())
