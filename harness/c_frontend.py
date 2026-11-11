"""Small, shared C frontend instruments for the census scripts.

The census tools must inspect Clang's AST and preprocessor stream rather than
re-parsing C source text.  This module keeps the executable selection and the
source-attributed preprocessor walk in one place.
"""

import json
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
CLANG_ENV = "LEAN_C_CLANG"
PROFILE_FLAGS = ["-std=c23", "-D_FORTIFY_SOURCE=0"]


def clang_executable():
    return os.environ.get(CLANG_ENV, "clang")


def run(args, **kwargs):
    return subprocess.run([clang_executable()] + list(args),
                          capture_output=True, text=True, **kwargs)


def version():
    result = run(["--version"])
    return (result.stdout or "").splitlines()[0] if result.stdout else "unknown"


def ast(path):
    result = run(PROFILE_FLAGS + ["-fsyntax-only", "-Xclang", "-ast-dump=json", str(path)])
    if result.returncode != 0:
        raise RuntimeError("clang rejected %s (exit %d): %s" %
                           (path, result.returncode, result.stderr[:2000]))
    if not result.stdout:
        raise RuntimeError("clang produced no AST for %s" % path)
    return json.loads(result.stdout)


def _marker(line):
    if not line.startswith("# "):
        return None
    fields = line.split()
    if len(fields) >= 3 and fields[1].isdigit():
        return fields[2].strip('"')
    return None


def preprocessor(path, mode):
    """Return source-attributed include/macro records from clang's stream."""
    result = run(PROFILE_FLAGS + ["-E"] + list(mode) + [str(path)])
    if result.returncode != 0:
        raise RuntimeError("clang preprocessing failed for %s: %s" %
                           (path, result.stderr[:2000]))
    source = str(Path(path).resolve())
    current = None
    records = []
    for line in result.stdout.splitlines():
        marker = _marker(line)
        if marker is not None:
            current = marker
            continue
        if current != source:
            continue
        if line.startswith("#include "):
            records.append(("include", line[len("#include "):].split(" /*", 1)[0].strip()))
        elif line.startswith("#define "):
            records.append(("define", line[len("#define "):].strip()))
    return records


def source_includes(path):
    return [value for kind, value in preprocessor(path, ["-dI"])
            if kind == "include"]


def source_macros(path):
    return [value for kind, value in preprocessor(path, ["-dD"])
            if kind == "define"]


def source_directives(path):
    """Directive names retained by Clang's preprocessor output."""
    result = run(PROFILE_FLAGS + ["-E", "-dD", "-dI", str(path)])
    if result.returncode != 0:
        raise RuntimeError("clang preprocessing failed for %s: %s" %
                           (path, result.stderr[:2000]))
    source = str(Path(path).resolve())
    current, directives = None, []
    for line in result.stdout.splitlines():
        marker = _marker(line)
        if marker is not None:
            current = marker
            continue
        if current != source or not line.startswith("#"):
            continue
        fields = line[1:].strip().split(None, 1)
        if fields and not fields[0].isdigit():
            directives.append(fields[0])
    return directives


def walk(node):
    if isinstance(node, dict):
        yield node
        for key in ("inner", "args"):
            for child in node.get(key) or []:
                yield from walk(child)
    elif isinstance(node, list):
        for child in node:
            yield from walk(child)


def source_nodes(tree, source):
    """Yield AST nodes attributed to one source using Clang's sticky locations."""
    target = Path(source).name
    current = None
    for node in walk(tree):
        for slot in (node.get("loc") or {},
                     (node.get("range") or {}).get("begin") or {},
                     (node.get("range") or {}).get("end") or {}):
            if slot.get("file"):
                current = Path(slot["file"]).name
            for nested in ("expansionLoc", "spellingLoc"):
                if (slot.get(nested) or {}).get("file"):
                    current = Path(slot[nested]["file"]).name
        if current == target:
            yield node
