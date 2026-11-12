#!/usr/bin/env python3
"""Print Python-lane Lean modules transitively importing changed sources.

This is the Python counterpart of ``check_sv_chain.sh --dependents``.  It
walks source imports, never oleans, and prints only dotted module names under
``LeanModels.Python`` and ``Examples.python`` in deterministic order.  A source file is not
its own dependent.
"""

import argparse
import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
IMPORT = re.compile(r"^\s*(?:(?:public|meta)\s+)*import\s+(?:all\s+)?([^\s]+)")


def module_name(path):
    rel = Path(path)
    if rel.is_absolute():
        rel = rel.relative_to(ROOT)
    rel = rel.with_suffix("")
    parts = list(rel.parts)
    if parts and parts[-1] == "__init__":
        parts.pop()
    return ".".join(parts)


def source_files():
    return sorted(p for base in (ROOT / "LeanModels", ROOT / "Examples")
                  for p in base.rglob("*.lean"))


def import_graph(files=None):
    files = source_files() if files is None else files
    if not files:
        raise RuntimeError("no Lean source files under LeanModels/ or Examples/")
    graph = {}
    for path in files:
        importer = module_name(path)
        imported = []
        for line in path.read_text(encoding="utf-8").splitlines():
            match = IMPORT.match(line)
            if match:
                imported.append(match.group(1).replace("«", "").replace("»", ""))
        graph[importer] = imported
    return graph


def seed_module(path):
    path = Path(path)
    if not path.is_absolute():
        path = ROOT / path
    return module_name(path)


def dependents(graph, seeds, allowed=("LeanModels.Python.", "Examples.python.")):
    reverse = {}
    for importer, imported in graph.items():
        for target in imported:
            reverse.setdefault(target, set()).add(importer)
    seen = set(seeds)
    front = set(seeds)
    while front:
        nxt = set()
        for target in front:
            nxt.update(reverse.get(target, ()))
        nxt -= seen
        seen.update(nxt)
        front = nxt
    return sorted(name for name in seen - set(seeds)
                  if any(name.startswith(prefix) for prefix in allowed))


def self_test():
    graph = {
        "LeanModels.Python.Semantics": [],
        "LeanModels.Python.Obs": ["LeanModels.Python.Semantics"],
        "LeanModels.Python.Surface": ["LeanModels.Python.Obs"],
        "Examples.python.tri.spec": ["LeanModels.Python.Surface"],
        "LeanModels.Sv.Other": ["LeanModels.Python.Semantics"],
    }
    got = dependents(graph, ["LeanModels.Python.Semantics"])
    assert got == ["Examples.python.tri.spec", "LeanModels.Python.Obs", "LeanModels.Python.Surface"]
    assert dependents(graph, ["LeanModels.Python.Surface"]) == ["Examples.python.tri.spec"]
    print("check_python_dependents self-test: 2 cases passed")


def main(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("paths", nargs="*")
    opts = parser.parse_args(argv)
    if opts.self_test:
        self_test()
        return 0
    if not opts.paths:
        parser.error("provide one or more changed Lean paths")
    try:
        graph = import_graph()
    except (OSError, RuntimeError) as error:
        print(f"check_python_dependents: {error}", file=sys.stderr)
        return 2
    seeds = [seed_module(path) for path in opts.paths]
    for name in dependents(graph, seeds):
        print(name)
    return 0


if __name__ == "__main__":
    sys.exit(main())
