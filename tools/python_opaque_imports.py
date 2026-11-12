#!/usr/bin/env python3
"""Measure the narrow CPython allowlist for the opaque-import abstraction.

Each module is imported in a fresh pinned CPython 3.9.25 interpreter.  The
measurement records stdout, stderr, the exception class, and changes to the
builtins dictionary.  It never imports a module in the survey process itself.
"""

import argparse
import hashlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
DEFAULT_MODULES = (
    "collections.abc", "contextvars", "email.base64mime", "email.charset",
    "importlib.machinery", "reprlib", "struct", "fnmatch", "unittest.util",
    "rsa_inverse",
)


def _probe(python, module, directory=None):
    code = r'''
import builtins, importlib, json, sys, traceback
if sys.argv[2]:
    sys.path.insert(0, sys.argv[2])
before = dict(builtins.__dict__)
result = {"module": sys.argv[1], "stdout": "", "stderr": "",
          "status": "ok", "exception": None, "builtins_changed": []}
try:
    importlib.import_module(sys.argv[1])
except BaseException as exc:
    result["status"] = "exception"
    result["exception"] = type(exc).__name__
result["builtins_changed"] = sorted(
    key for key, value in before.items()
    if key not in builtins.__dict__ or builtins.__dict__[key] is not value
) + sorted(key for key in builtins.__dict__ if key not in before)
print(json.dumps(result, sort_keys=True))
'''
    proc = subprocess.run(
        [python, "-I", "-c", code, module, str(directory or "")],
        capture_output=True, text=True, timeout=30,
    )
    if proc.returncode != 0:
        return {"module": module, "status": "runner-error",
                "stdout": proc.stdout, "stderr": proc.stderr,
                "returncode": proc.returncode, "eligible": False}
    try:
        result = json.loads(proc.stdout)
    except json.JSONDecodeError:
        return {"module": module, "status": "printed-or-malformed",
                "stdout": proc.stdout, "stderr": proc.stderr, "eligible": False}
    # The JSON line is the probe's protocol; anything before it is module output.
    lines = proc.stdout.splitlines()
    result["stdout"] = "\n".join(lines[:-1]) + ("\n" if len(lines) > 1 else "")
    result["stderr"] = proc.stderr
    if result["stdout"] or result["stderr"] or result["status"] != "ok":
        result["eligible"] = False
    else:
        result["eligible"] = not result["builtins_changed"]
    return result


def _hash(path):
    digest = hashlib.sha256()
    with open(path, "rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def measure(python, modules, rsa_path=None):
    corpus = {row["module"]: row for row in json.loads(
        (ROOT / "harness/library_corpus.json").read_text(encoding="utf-8")
    )["modules"]}
    rows = []
    for module in modules:
        if module == "rsa_inverse":
            if rsa_path is None:
                raise ValueError("rsa_inverse needs --rsa-path")
            path = Path(rsa_path)
            directory = str(path.parent)
            source_hash = _hash(path)
        else:
            row = corpus.get(module)
            if row is None:
                raise ValueError("module is absent from the pinned corpus: " + module)
            path = Path(row["file"])
            directory = None
            source_hash = row["sha256"]
        probe = _probe(python, module, directory)
        rows.append({"module": module, "sha256": source_hash,
                     "file": str(path), "probe": probe,
                     "eligible": bool(probe.get("eligible"))})
    return {"python": subprocess.check_output([python, "--version"],
                                                stderr=subprocess.STDOUT,
                                                text=True).strip(),
            "modules": rows}


def self_test(python):
    with tempfile.TemporaryDirectory(prefix="opaque-import-") as directory:
        root = Path(directory)
        (root / "printing_mod.py").write_text("print('printed')\n")
        (root / "raising_mod.py").write_text("raise RuntimeError('boom')\n")
        (root / "builtin_mod.py").write_text(
            "import builtins\nbuiltins.len = lambda x: 0\n")
        for name in ("printing_mod", "raising_mod", "builtin_mod"):
            result = _probe(python, name, root)
            assert not result["eligible"], (name, result)
        (root / "quiet_mod.py").write_text("value = 1\n")
        assert _probe(python, "quiet_mod", root)["eligible"]
    print("python_opaque_imports: self-test passed (printing, raising, builtin-rebind, quiet)")


def main(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--python", default="python3.9")
    parser.add_argument("--out")
    parser.add_argument("--rsa-path", default="Examples/python/rsa_inverse/rsa_inverse.py")
    parser.add_argument("modules", nargs="*")
    opts = parser.parse_args(argv)
    if opts.self_test:
        self_test(opts.python)
        return 0
    modules = tuple(opts.modules) or DEFAULT_MODULES
    try:
        result = measure(opts.python, modules, opts.rsa_path)
    except (OSError, ValueError, subprocess.SubprocessError) as exc:
        print("python_opaque_imports: %s" % exc, file=sys.stderr)
        return 2
    eligible = [row for row in result["modules"] if row["eligible"]]
    if opts.out:
        Path(opts.out).write_text(json.dumps(result, indent=2, sort_keys=True) + "\n",
                                   encoding="utf-8")
    print("opaque import measurement: %d/%d eligible" %
          (len(eligible), len(result["modules"])))
    for row in result["modules"]:
        print("  %-24s %s" % (row["module"], "eligible" if row["eligible"] else "refused"))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
