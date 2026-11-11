#!/usr/bin/env python3
"""Differential refusal rows for unrepresented C type declarator spellings."""

import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
CLANG = os.environ.get("LEANC_CLANG", "clang")
ROWS = {
    "function-pointer": "int f(int x) { return x; } int main(void) { int (*p)(int) = f; return p(1); }",
    "nested-array": "int main(void) { int a[2][3] = {{1, 2, 3}, {4, 5, 6}}; return a[1][2]; }",
    "postfix-qualified-pointer": "int main(void) { int x = 1; int *const p = &x; return *p; }",
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
    with tempfile.TemporaryDirectory(prefix="c-type-spelling-guard-") as temp:
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
            manifest = work / (name + ".manifest.json")
            manifest.write_text(json.dumps({
                "tests": [{"name": name, "status": "parsed",
                           "envelope": str(envelope), "why": ""}]
            }))
            model = run(["lake", "exe", "c-torture-run", str(manifest)])
            if model.returncode or (name + "\trefused-unsupported\t") not in model.stdout:
                raise RuntimeError(name + ": expected refusal, got %r %r" %
                                   (model.stdout, model.stderr))
            print(name + ": REFUSE")
    return 0


if __name__ == "__main__":
    sys.exit(main())
