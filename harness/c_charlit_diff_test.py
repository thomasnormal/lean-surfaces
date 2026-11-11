#!/usr/bin/env python3
"""Differential rows for signed ordinary C character constants."""

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
    "ascii": "'a' == 97",
    "high-hex": "'\\xff' == -1",
    "high-octal": "'\\377' == -1",
    "high-80": "'\\x80' == -128",
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
    with tempfile.TemporaryDirectory(prefix="c-charlit-diff-") as temp:
        work = Path(temp)
        for name, condition in ROWS.items():
            source = work / (name + ".c")
            source.write_text("int main(void) { return (" + condition + ") ? 0 : 1; }\n")
            native = work / name
            compiled = run([clang, "--no-default-config", "-std=c23", "-O0",
                            str(source), "-o", str(native)])
            if compiled.returncode:
                raise RuntimeError(name + ": native compile failed: " + compiled.stderr)
            native_run = run([str(native)])
            if native_run.returncode != 0:
                raise RuntimeError(name + ": native exit %s" % native_run.returncode)
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
            if model.returncode or (name + "\tpassed\t") not in model.stdout:
                raise RuntimeError(name + ": expected MATCH, got %r %r" %
                                   (model.stdout, model.stderr))
            print(name + ": MATCH")
    return 0


if __name__ == "__main__":
    sys.exit(main())
