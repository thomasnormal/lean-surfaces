#!/usr/bin/env python3
"""Verify TinyXML-2 literals are exactly current exporter output.

The canonical probe is intentionally external. Set LEANCPP_TINYXML2_PROBE to
its captured JSON and run this gate on a machine with the pinned Lean toolchain.
Missing capture inputs are an explicit error, never a default or a guessed
literal.
"""

import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
EXAMPLE = ROOT / "Examples/cpp/tinyxml2"
PROBE_ENV = "LEANCPP_TINYXML2_PROBE"


def fail(message):
    print("tinyxml2-literals: ERROR: " + message, file=sys.stderr)
    return 2


def manifest_entries():
    entries = []
    callable_manifest = json.loads((EXAMPLE / "provenance.json").read_text(encoding="utf-8"))
    entries.append(("provenance.json", "export_callable.lean", "IsUTF8Continuation.lean",
                    callable_manifest["probe_ast_path"], callable_manifest["literal_sha256"]))
    for manifest_name, exporter, key in (
        ("member-getters-provenance.json", "export_member_getter.lean", "literal_sha256"),
        ("class-subobjects-provenance.json", "export_class_hierarchy.lean", "literal_sha256"),
    ):
        manifest = json.loads((EXAMPLE / manifest_name).read_text(encoding="utf-8"))
        for literal, path in manifest["paths"].items():
            entries.append((manifest_name, exporter, literal, path,
                            manifest[key][literal]))
    return entries


def main():
    probe = os.environ.get(PROBE_ENV)
    if not probe:
        return fail(PROBE_ENV + " is required; the canonical probe is external")
    probe_path = Path(probe).resolve()
    if not probe_path.is_file():
        return fail("probe does not exist: " + str(probe_path))
    lake = shutil.which("lake")
    if lake is None:
        return fail("lake is unavailable")
    with tempfile.TemporaryDirectory(prefix="tinyxml2-literals-") as temp:
        for manifest_name, exporter, literal, path, expected_hash in manifest_entries():
            namespace = "Examples.cpp.tinyxml2." + Path(literal).stem
            command = [lake, "env", "lean", "-j", "1", "--run",
                       "extractors/cpp/" + exporter, str(probe_path),
                       ",".join(str(part) for part in path), namespace]
            result = subprocess.run(command, cwd=ROOT, capture_output=True,
                                    text=True, timeout=180)
            if result.returncode:
                return fail("%s %s: exporter failed:\n%s" %
                            (manifest_name, literal, result.stderr))
            output = result.stdout.encode("utf-8")
            target = (EXAMPLE / literal).read_bytes()
            if output != target:
                return fail("%s %s: committed literal differs from exporter output" %
                            (manifest_name, literal))
            if hashlib.sha256(target).hexdigest() != expected_hash:
                return fail("%s %s: literal_sha256 pin is stale" %
                            (manifest_name, literal))
            print("MATCH", literal)
    return 0


if __name__ == "__main__":
    sys.exit(main())
