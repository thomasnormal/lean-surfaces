#!/usr/bin/env python3
"""Differential row for pointer arithmetic past an array member."""

import json
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
    source_text = """struct S { int a[2]; int b; };
int main(void) {
  struct S s = {{1, 2}, 3};
  return s.a[2];
}
"""
    with tempfile.TemporaryDirectory(prefix="c-subobject-bounds-") as temp:
        work = Path(temp)
        source = work / "sub.c"
        source.write_text(source_text)
        native = work / "sub"
        compiled = run([clang, "--no-default-config", "-std=c23", "-O0",
                        str(source), "-o", str(native)])
        if compiled.returncode:
            raise RuntimeError("native compile failed: " + compiled.stderr)
        native_run = run([str(native)])
        if native_run.returncode != 3:
            raise RuntimeError("expected native exit 3, got %s" % native_run.returncode)

        envelope = work / "sub.json"
        extracted = run([sys.executable, "extractors/c/extract.py", str(source), "-o", str(envelope)])
        if extracted.returncode:
            raise RuntimeError("extraction failed: " + extracted.stderr)
        manifest = work / "manifest.json"
        manifest.write_text(json.dumps({
            "tests": [{"name": "subobject", "status": "parsed",
                       "envelope": str(envelope), "why": ""}]
        }))
        model = run(["lake", "exe", "c-torture-run", str(manifest)])
        if (model.returncode or "subobject\trefused-ub\t" not in model.stdout or
                "outOfBounds" not in model.stdout):
            raise RuntimeError("expected subobject-bound refusal, got %r %r" %
                               (model.stdout, model.stderr))
        print("array-member-overrun: REFUSE (native exit %s)" % native_run.returncode)
    return 0


if __name__ == "__main__":
    sys.exit(main())
