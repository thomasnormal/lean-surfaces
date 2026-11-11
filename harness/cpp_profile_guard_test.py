#!/usr/bin/env python3
"""Pin the C++ artifact's LP64/signed-char profile admission boundary."""

import os
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
CLANG = os.environ.get("LEANCPP_CLANG", "clang++")


def run(args):
    return subprocess.run(args, cwd=ROOT, text=True, capture_output=True, timeout=120)


def main():
    with tempfile.TemporaryDirectory(prefix="cpp-profile-guard-") as temp:
        source = Path(temp) / "profile.cpp"
        output = Path(temp) / "profile.json"
        source.write_text("int profile_probe() { return sizeof(long) == 8 ? 0 : 1; }\n")
        extracted = run([sys.executable, "extractors/cpp/extract.py", str(source),
                         "--clang", CLANG, "--out", str(output)])
        if extracted.returncode:
            raise RuntimeError("default profile extraction failed: " + extracted.stderr)
        payload = __import__("json").loads(output.read_text())
        macros = payload["frontend"]["predefined_macros"]
        required = ("#define __CHAR_BIT__ 8", "#define __SIZEOF_SHORT__ 2",
                    "#define __SIZEOF_INT__ 4", "#define __SIZEOF_LONG__ 8",
                    "#define __SIZEOF_LONG_LONG__ 8",
                    "#define __SIZEOF_POINTER__ 8")
        if any(marker not in macros.splitlines() for marker in required):
            raise RuntimeError("artifact omitted a required LP64 macro")
        refused = run([sys.executable, "extractors/cpp/extract.py", str(source),
                       "--clang", CLANG, "--", "-m32"])
        if refused.returncode == 0 or "outside" not in refused.stderr:
            raise RuntimeError("profile-changing -m32 flag was admitted: %r" % refused.stderr)
        print("cpp-lp64-profile: MATCH")
        print("cpp-profile-changing-flag: REFUSE")
    return 0


if __name__ == "__main__":
    sys.exit(main())
