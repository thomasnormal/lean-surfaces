#!/usr/bin/env python3
"""Capture the PINNED PLATFORM INVENTORY (docs/memory-model.md
paragraph "Import forms (Pass 0)") from one CPython installation.

The inventory is the set of top-level module names the pinned
interpreter SHIPS: ``sys.builtin_module_names``, the ``lib-dynload``
extension stems, and the top-level stdlib modules/packages (``*.py``
stems and ``__init__.py`` package directories at the stdlib root).
Scope is the interpreter AS SHIPPED — site-packages has no
``__init__.py`` and contributes nothing, and nothing under it is ever
listed. The claim the file backs is the extractor's absent-module
admission: a from-import of a name NOT in this set raises
``ModuleNotFoundError`` under the pinned interpreter, so the model's
unconditional Pass 0 raise is CPython's own behavior there.

Discipline (the census C-module table, the ``isPyBuiltinName``
precedent): the interpreter is ASKED by subprocess and never imported,
no absence is ever guessed, and the output is committed as data
(``platform_inventory.json``) so the extractor reads a reviewed file,
not a live machine.

Usage:
    python3 extractors/python/capture_inventory.py [CPYTHON]

CPYTHON defaults to ``python3.9`` (the pinned oracle). Writes
``platform_inventory.json`` next to this script. Python 3.9 compatible.
"""

import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "platform_inventory.json")


def capture(cpython):
    """The inventory of one installed interpreter — asked, never imported."""
    out = subprocess.run(
        [cpython, "-c",
         "import sys, sysconfig;"
         "print(sysconfig.get_paths()['stdlib']);"
         "print(' '.join(sys.builtin_module_names));"
         "print(sys.version.split()[0])"],
        capture_output=True, text=True)
    if out.returncode != 0:
        raise SystemExit("capture_inventory: %s is not runnable: %s"
                         % (cpython, out.stderr.strip()))
    lib, builtins, version = out.stdout.splitlines()[:3]
    modules = set(builtins.split())
    dynload = os.path.join(lib, "lib-dynload")
    if os.path.isdir(dynload):
        for f in os.listdir(dynload):
            if f.endswith((".so", ".pyd", ".dylib")):
                modules.add(f.split(".")[0])
    for entry in os.listdir(lib):
        p = os.path.join(lib, entry)
        if entry.endswith(".py") and os.path.isfile(p):
            modules.add(entry[:-3])
        elif os.path.isdir(p) and os.path.isfile(
                os.path.join(p, "__init__.py")):
            modules.add(entry)
    return version, sorted(modules)


def main(argv):
    cpython = argv[1] if len(argv) > 1 else "python3.9"
    version, modules = capture(cpython)
    payload = {
        "comment": "PINNED PLATFORM INVENTORY (docs/memory-model.md "
                   "paragraph 'Import forms (Pass 0)'): top-level module "
                   "names the pinned interpreter ships, captured by "
                   "subprocess (never imported) by capture_inventory.py. "
                   "The extractor's absent-module admission reads this "
                   "file; regenerate ONLY against the pinned oracle.",
        "cpython": version,
        "captured_by": "extractors/python/capture_inventory.py",
        "modules": modules,
    }
    with open(OUT, "w", encoding="utf-8") as f:
        json.dump(payload, f, indent=1)
        f.write("\n")
    print("%s: %d modules (cpython %s)" % (OUT, len(modules), version))


if __name__ == "__main__":
    main(sys.argv)
