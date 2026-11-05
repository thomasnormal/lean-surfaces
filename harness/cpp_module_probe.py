#!/usr/bin/env python3
"""Measure whether the pinned Clang JSON AST retains C++ module declarations.

This probe does not parse C++ source. It compiles one fixed C++23 module-unit
witness and inspects only Clang's JSON AST envelope, recording the frontend
boundary that must be closed before a module tier can be admitted.
"""

from __future__ import print_function

import argparse
import json
import os
import pathlib
import shutil
import subprocess
import tempfile


PINNED = "21.1.8"
SOURCE = "export module m;\n"
MODULE_SOURCE = "export module m; export int f(){return 1;}\n"
IMPORT_SOURCE = "import m; int g(){return f();}\n"


def frontend():
    requested = os.environ.get("LEANCPP_CLANG") or "clang++"
    executable = (shutil.which(requested)
                  if os.path.basename(requested) == requested else requested)
    if not executable or not os.path.exists(executable):
        return None, "pinned Clang/LLVM %s is unavailable" % PINNED
    result = subprocess.run([executable, "--version"], capture_output=True,
                            text=True, check=False, timeout=20)
    version = (result.stdout + result.stderr).strip()
    if result.returncode != 0 or PINNED not in version:
        return None, "Clang is not pinned to %s: %s" % (PINNED, version.splitlines()[0] if version else "unknown")
    return executable, version.splitlines()[0]


def kinds(value):
    found = []
    if isinstance(value, dict):
        if isinstance(value.get("kind"), str):
            found.append(value["kind"])
        for child in value.values():
            found.extend(kinds(child))
    elif isinstance(value, list):
        for child in value:
            found.extend(kinds(child))
    return found


def nodes(value, wanted):
    found = []
    if isinstance(value, dict):
        if value.get("kind") == wanted:
            found.append(value)
        for child in value.values():
            found.extend(nodes(child, wanted))
    elif isinstance(value, list):
        for child in value:
            found.extend(nodes(child, wanted))
    return found


def measure():
    clang, version = frontend()
    if clang is None:
        return {"format": "cpp-module-frontend-1", "status": "ORACLE",
                "frontend": version, "source": SOURCE,
                "execution": "not-attempted"}
    with tempfile.TemporaryDirectory(prefix="cpp-module-probe-") as directory:
        source = pathlib.Path(directory) / "module.cppm"
        pcm = pathlib.Path(directory) / "m.pcm"
        source.write_text(MODULE_SOURCE, encoding="utf-8")
        result = subprocess.run(
            [clang, "-std=c++23", "-x", "c++-module", "--precompile",
             str(source), "-o", str(pcm)], capture_output=True,
            text=True, check=False, timeout=60)
        if result.returncode != 0:
            return {"format": "cpp-module-frontend-1", "status": "ORACLE",
                    "frontend": version, "source": SOURCE,
                    "execution": "compile-failed",
                    "diagnostic": (result.stderr or result.stdout)[-1000:]}
        importer = pathlib.Path(directory) / "import.cpp"
        importer.write_text(IMPORT_SOURCE, encoding="utf-8")
        result = subprocess.run(
            [clang, "-std=c++23", "-fmodule-file=m=" + str(pcm),
             "-fsyntax-only", "-w", "-Xclang", "-ast-dump=json", str(importer)],
            capture_output=True, text=True, check=False, timeout=60)
        if result.returncode != 0:
            return {"format": "cpp-module-frontend-1", "status": "ORACLE",
                    "frontend": version, "source": SOURCE,
                    "execution": "import-compile-failed",
                    "diagnostic": (result.stderr or result.stdout)[-1000:]}
        try:
            ast = json.loads(result.stdout)
        except ValueError as error:
            return {"format": "cpp-module-frontend-1", "status": "ORACLE",
                    "frontend": version, "source": SOURCE,
                    "execution": "import-malformed-json", "diagnostic": str(error)}
        import_nodes = nodes(ast, "ImportDecl")
        observed = sorted(set(kinds(ast)))
        return {"format": "cpp-module-frontend-1", "status": "REFUSE",
                "frontend": version, "source": SOURCE,
                "execution": "module-and-import-compiled", "root": ast.get("kind"),
                "module_node": "ModuleDecl" in observed,
                "import_node": bool(import_nodes),
                "import_fields": sorted(import_nodes[0].keys()) if import_nodes else [],
                "import_identity": all(
                    any(key in node for key in ("name", "module", "importedModule", "referencedDecl"))
                    for node in import_nodes),
                "observed_module_kinds": [kind for kind in observed if "Module" in kind]}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", type=pathlib.Path)
    options = parser.parse_args()
    result = measure()
    encoded = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if options.json:
        options.json.write_text(encoded, encoding="utf-8")
    print(encoded, end="")
    return 0 if result["status"] == "REFUSE" else 2


if __name__ == "__main__":
    raise SystemExit(main())
