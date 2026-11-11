#!/usr/bin/env python3
"""Differential rows for C integer promotions in compound assignment."""

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
    "signed-char-plus": ("int main(void) { signed char s = 127; s += 1; return s; }", "match"),
    "unsigned-char-shift": ("int main(void) { unsigned char u = 1; u <<= 8; return u; }", "match"),
    "bool-increment": ("int main(void) { _Bool b = 1; b++; return b; }", "match"),
    "mixed-signed-unsigned": ("int main(void) { int i = 2147483647; i += 1u; return i; }", "match"),
    "ushort-overflow": ("int main(void) { unsigned short a = 65535; a *= a; return a; }", "refuse"),
}


def run(args, **kwargs):
    return subprocess.run(args, cwd=ROOT, text=True, capture_output=True, timeout=120, **kwargs)


def walk(value):
    if isinstance(value, dict):
        if value.get("kind") == "CompoundAssignOperator":
            yield value
        for child in value.values():
            yield from walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from walk(child)


def main():
    clang = shutil.which(CLANG)
    if not clang:
        raise RuntimeError("LEANC_CLANG must select Clang 21.1.8")
    version = run([clang, "--version"])
    first = version.stdout.splitlines()[0]
    if not first.startswith("clang version 21.1.8 "):
        raise RuntimeError("expected Clang 21.1.8, got " + first)
    print("C oracle:", first)
    with tempfile.TemporaryDirectory(prefix="c-compound-diff-") as temp:
        work = Path(temp)
        for name, (body, expectation) in ROWS.items():
            source = work / (name + ".c")
            source.write_text(body + "\n")
            native = work / name
            flags = [clang, "--no-default-config", "-std=c23", "-O0"]
            if expectation == "refuse":
                flags += ["-fsanitize=undefined", "-fno-sanitize-recover=all"]
            compiled = run(flags + [str(source), "-o", str(native)])
            if compiled.returncode:
                raise RuntimeError(name + ": native compile failed: " + compiled.stderr)
            native_run = run([str(native)])
            envelope = work / (name + ".json")
            extracted = run([sys.executable, "extractors/c/extract.py", str(source), "-o", str(envelope)])
            if extracted.returncode:
                raise RuntimeError(name + ": extraction failed: " + extracted.stderr)
            compounds = list(walk(json.loads(envelope.read_text())))
            if compounds and (not compounds[0].get("compute_lhs_type") or
                              not compounds[0].get("compute_result_type")):
                raise RuntimeError(name + ": missing Clang promotion evidence")
            model = run(["lake", "env", "lean", "-j", "1", "--run",
                         "harness/c_filler_runner.lean", str(envelope)])
            if expectation == "refuse":
                if model.returncode != 3:
                    raise RuntimeError(name + ": expected model refusal, got %s %r" %
                                       (model.returncode, model.stdout))
                print(name + ": REFUSE (native UBSan status %s)" % native_run.returncode)
            else:
                model_value = int(model.stdout.strip()) if model.stdout.strip() else None
                # The host process exposes C's `return int` through an
                # unsigned 8-bit exit status; compare that projection while
                # retaining the model's mathematical signed value in output.
                if model.returncode or model_value is None or model_value % 256 != native_run.returncode:
                    raise RuntimeError(name + ": native=%s model=%r stderr=%r" %
                                       (native_run.returncode, model.stdout, model.stderr))
                print(name + ": MATCH model=" + str(model_value) +
                      " exit=" + str(native_run.returncode))
    return 0


if __name__ == "__main__":
    sys.exit(main())
