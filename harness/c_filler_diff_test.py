#!/usr/bin/env python3
"""Compare Clang's real array initializer AST with the C interpreter."""

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
    "designated-gap": "int a[5] = {[3] = 7}; return a[0] + 2*a[1] + 3*a[2] + 4*a[3] + 5*a[4];",
    "mixed-gap": "int b[6] = {1, [4] = 9}; return b[0] + 2*b[1] + 3*b[2] + 4*b[3] + 5*b[4] + 6*b[5];",
    "partial-tail": "int a[5] = {1, 2, 3}; return a[0] + 2*a[1] + 3*a[2] + 4*a[3] + 5*a[4];",
    "full": "int a[3] = {2, 3, 4}; return a[0] + 2*a[1] + 3*a[2];",
    "all-zero": "int a[4] = {}; return a[0] + a[1] + a[2] + a[3];",
}


def run(args, **kwargs):
    return subprocess.run(args, cwd=ROOT, text=True, capture_output=True, timeout=120, **kwargs)


def find_initializers(value):
    if isinstance(value, dict):
        if value.get("kind") == "InitListExpr":
            yield value
        for child in value.values():
            yield from find_initializers(child)
    elif isinstance(value, list):
        for child in value:
            yield from find_initializers(child)


def main():
    clang = shutil.which(CLANG)
    if not clang:
        raise RuntimeError("LEANC_CLANG must select Clang 21.1.8")
    version = run([clang, "--version"])
    first = version.stdout.splitlines()[0]
    if not first.startswith("clang version 21.1.8 "):
        raise RuntimeError("expected Clang 21.1.8, got " + first)
    print("C oracle:", first)
    environment = dict(os.environ)
    environment["PATH"] = str(Path(clang).resolve().parent) + os.pathsep + environment.get("PATH", "")
    with tempfile.TemporaryDirectory(prefix="c-filler-diff-") as temp:
        work = Path(temp)
        for name, body in ROWS.items():
            source = work / (name + ".c")
            source.write_text("int main(void) { " + body + " }\n")
            native = work / name
            compiled = run([clang, "--no-default-config", "-std=c23", "-O0", str(source), "-o", str(native)])
            if compiled.returncode:
                raise RuntimeError(name + ": native compile failed: " + compiled.stderr)
            expected = run([str(native)]).returncode
            envelope = work / (name + ".json")
            extracted = run([sys.executable, "extractors/c/extract.py", str(source), "-o", str(envelope)], env=environment)
            if extracted.returncode:
                raise RuntimeError(name + ": extraction failed: " + extracted.stderr)
            payload = json.loads(envelope.read_text())
            init, = list(find_initializers(payload["translation_unit"]))
            if "array_filler" not in init:
                raise RuntimeError(name + ": missing required array_filler field")
            dumped = run([clang, "--no-default-config", "-std=c23", "-D_FORTIFY_SOURCE=0",
                          "-fsyntax-only", "-Xclang", "-ast-dump=json", str(source)])
            if dumped.returncode:
                raise RuntimeError(name + ": Clang AST dump failed: " + dumped.stderr)
            raw, = list(find_initializers(json.loads(dumped.stdout)))
            raw_filler = raw.get("array_filler")
            projected = init["array_filler"]
            shape = lambda nodes: None if nodes is None else [(node.get("kind"), node.get("value")) for node in nodes]
            if shape(raw_filler) != shape(projected):
                raise RuntimeError(name + ": Clang filler positions changed during extraction")
            if name in ("designated-gap", "mixed-gap"):
                filler = init["array_filler"]
                if not filler or sum(node["kind"] == "ImplicitValueInitExpr" for node in filler) < 2:
                    raise RuntimeError(name + ": missing positional implicit initializers")
            model = run(["lake", "env", "lean", "-j", "1", "--run", "harness/c_filler_runner.lean", str(envelope)])
            if model.returncode or model.stdout.strip() != str(expected):
                raise RuntimeError(name + ": native=%s model=%r stderr=%r" % (expected, model.stdout, model.stderr))
            print(name + ": MATCH " + str(expected))
            if name == "designated-gap":
                del init["array_filler"]
                envelope.write_text(json.dumps(payload))
                legacy = run(["lake", "env", "lean", "-j", "1", "--run", "harness/c_filler_runner.lean", str(envelope)])
                if legacy.returncode != 2 or "array_filler" not in legacy.stderr:
                    raise RuntimeError("legacy lossy envelope was not refused: " + legacy.stderr)
                print("legacy lossy envelope: REFUSE")
    return 0


if __name__ == "__main__":
    sys.exit(main())
