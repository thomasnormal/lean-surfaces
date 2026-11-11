#!/usr/bin/env python3
"""Check that two clang AST extractions of one source are byte-identical."""

import os
import subprocess
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
EXTRACT = ROOT / "extractors" / "c" / "extract.py"


def main():
    with tempfile.TemporaryDirectory(prefix="c-extract-determinism-") as d:
        src = Path(d) / "ids.c"
        one = Path(d) / "one.json"
        two = Path(d) / "two.json"
        src.write_text("int f(int x) { goto done; done: return x; }\n")
        env = os.environ.copy()
        for out in (one, two):
            p = subprocess.run(
                [sys.executable, str(EXTRACT), str(src), "-o", str(out)],
                cwd=ROOT, env=env, text=True, capture_output=True,
            )
            if p.returncode:
                print(p.stderr, file=sys.stderr, end="")
                return 1
        if one.read_bytes() != two.read_bytes():
            print("c_extract_determinism: two extractions differ", file=sys.stderr)
            return 1
        if b"0x" in one.read_bytes():
            print("c_extract_determinism: raw clang address remains", file=sys.stderr)
            return 1
    print("c_extract_determinism: ok")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
