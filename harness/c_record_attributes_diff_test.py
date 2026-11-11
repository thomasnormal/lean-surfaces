#!/usr/bin/env python3
"""Differential refusal row for record packing and alignment attributes."""

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


def records(value):
    if isinstance(value, dict):
        if value.get("kind") == "RecordDecl":
            yield value
        for child in value.values():
            yield from records(child)
    elif isinstance(value, list):
        for child in value:
            yield from records(child)


def main():
    clang = shutil.which(CLANG)
    if not clang:
        raise RuntimeError("LEANC_CLANG must select Clang 21.1.8")
    first = run([clang, "--version"]).stdout.splitlines()[0]
    if not first.startswith("clang version 21.1.8 "):
        raise RuntimeError("expected Clang 21.1.8, got " + first)
    print("C oracle:", first)
    source_text = """#pragma pack(push, 1)
struct P { char c; int i; };
#pragma pack(pop)
struct Q { char c; int i; } __attribute__((packed));
struct R { char c; _Alignas(32) int i; };
int main(void) {
  return (sizeof(struct P) == 5 && sizeof(struct Q) == 5 &&
          sizeof(struct R) == 64) ? 0 : 1;
}
"""
    with tempfile.TemporaryDirectory(prefix="c-record-attributes-") as temp:
        work = Path(temp)
        source = work / "attrs.c"
        source.write_text(source_text)
        native = work / "attrs"
        compiled = run([clang, "--no-default-config", "-std=c23", "-O0",
                        str(source), "-o", str(native)])
        if compiled.returncode:
            raise RuntimeError("native compile failed: " + compiled.stderr)
        native_run = run([str(native)])
        if native_run.returncode != 0:
            raise RuntimeError("native attribute row returned %s" % native_run.returncode)

        envelope = work / "attrs.json"
        extracted = run([sys.executable, "extractors/c/extract.py", str(source), "-o", str(envelope)])
        if extracted.returncode:
            raise RuntimeError("extraction failed: " + extracted.stderr)
        payload = json.loads(envelope.read_text())
        by_name = {r.get("name"): r for r in records(payload)}
        expected = {
            "P": "MaxFieldAlignmentAttr",
            "Q": "PackedAttr",
            "R": "AlignedAttr",
        }
        for name, attr in expected.items():
            found = [f.get("c_kind") for f in by_name[name]["fields"]
                     if f.get("kind") == "Unsupported"]
            if attr not in found:
                raise RuntimeError("%s attribute was dropped: %r" % (name, found))

        manifest = work / "manifest.json"
        manifest.write_text(json.dumps({
            "tests": [{"name": "attrs", "status": "parsed",
                       "envelope": str(envelope), "why": ""}]
        }))
        model = run(["lake", "exe", "c-torture-run", str(manifest)])
        if model.returncode or "attrs\trefused-unsupported\t" not in model.stdout:
            raise RuntimeError("expected attribute refusal, got %r %r" %
                               (model.stdout, model.stderr))
        print("record-attributes: REFUSE (native exit %s)" % native_run.returncode)
    return 0


if __name__ == "__main__":
    sys.exit(main())
