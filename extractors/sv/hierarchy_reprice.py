#!/usr/bin/env python3
"""Reprice files blocked solely by ``Hierarchy:ports``.

This read-only companion to ``census.py`` runs extraction in process, keeps
only files whose complete Unsupported set is the port wall, and measures the
actual concrete child instances that caused it.  Connection counts are taken
from the elaborated frontend symbols, not from source-text regular
expressions; file counts overlap when a file contains several instances.
"""

import argparse
import collections
import json
import pathlib
import re
import sys

from pyslang.ast import Compilation
from pyslang.syntax import SyntaxTree

REPO = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO / "extractors" / "sv"))
import extract  # noqa: E402

INCLUDE_RE = re.compile(r'^\s*`include\s*(?:["<`])', re.M)


def walk(node):
    """Walk an envelope value, yielding dictionary nodes."""
    if isinstance(node, dict):
        yield node
        for value in node.values():
            yield from walk(value)
    elif isinstance(node, list):
        for value in node:
            yield from walk(value)


def symbol_kind(node):
    return str(getattr(node, "kind", "")).split(".")[-1]


def child_instances(instance):
    """Yield concrete nested instances below one top instance."""
    if symbol_kind(instance) == "Instance":
        yield instance
        for member in instance.body:
            yield from child_instances(member)
        return
    try:
        for member in instance:
            yield from child_instances(member)
    except TypeError:
        return


def connection_kind(connection):
    expression = getattr(connection, "expression", None)
    if expression is None:
        return "empty"
    return symbol_kind(expression)


def instance_shape(instance):
    """Return a stable shape for one port-bearing child instance."""
    ports = list(getattr(instance.body, "portList", []) or [])
    connections = list(getattr(instance, "portConnections", []) or [])
    directions = tuple(sorted(
        str(getattr(port, "direction", "")).split(".")[-1]
        for port in ports
    ))
    connection_kinds = tuple(connection_kind(connection)
                              for connection in connections)
    if not connection_kinds or all(kind == "empty" for kind in connection_kinds):
        completeness = "unconnected"
    elif any(kind == "empty" for kind in connection_kinds):
        completeness = "partial"
    else:
        completeness = "connected"
    return completeness, directions, connection_kinds


def one_file(path):
    data = path.read_bytes()
    text = data.decode("utf-8")
    if INCLUDE_RE.search(text):
        return "skip_include", []
    tree = SyntaxTree.fromText(text, name=path.as_posix())
    compilation = Compilation()
    compilation.addSyntaxTree(tree)
    extract._SOURCE_BYTES = data
    envelope = extract.convert_design(tree.sourceManager, compilation)
    unsupported = [node for node in walk(envelope)
                   if node.get("kind") == "Unsupported"]
    kinds = {node.get("sv_kind") for node in unsupported}
    if kinds != {"Hierarchy:ports"}:
        return "other", []

    top_ids = {id(instance) for instance in compilation.getRoot().topInstances}
    shapes = []
    for top in compilation.getRoot().topInstances:
        for instance in child_instances(top):
            if id(instance) in top_ids or not getattr(instance, "isModule", False):
                continue
            if getattr(instance.body, "portList", None):
                shapes.append(instance_shape(instance))
    return "ports_only", shapes


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", required=True, type=pathlib.Path,
                        help="chapter-scoped sv-tests-2 tests directory")
    args = parser.parse_args(argv)

    files = sorted(args.corpus.glob("chapter-*/*.sv"))
    completeness = collections.Counter()
    directions = collections.Counter()
    connection_kinds = collections.Counter()
    files_by_completeness = collections.defaultdict(set)
    port_files = 0
    port_instances = 0
    ports = 0
    skipped = 0
    errors = 0

    for path in files:
        try:
            status, shapes = one_file(path)
        except Exception as exc:  # keep the measurement loud and complete
            print(f"error: {path}: {exc}", file=sys.stderr)
            errors += 1
            continue
        if status == "skip_include":
            skipped += 1
        elif status == "ports_only":
            port_files += 1
            for complete, dirs, kinds in shapes:
                port_instances += 1
                ports += len(dirs)
                completeness[complete] += 1
                files_by_completeness[complete].add(path.as_posix())
                directions[','.join(dirs)] += 1
                for kind in kinds:
                    connection_kinds[kind] += 1

    result = {
        "corpus_files": len(files),
        "ports_only_files": port_files,
        "port_instances": port_instances,
        "ports": ports,
        "include_skips": skipped,
        "errors": errors,
        "completeness": {
            name: {"instances": completeness[name],
                   "files": len(files_by_completeness[name])}
            for name in sorted(completeness)
        },
        "directions": {
            name: count for name, count in sorted(directions.items())
        },
        "connection_expressions": {
            name: count for name, count in sorted(connection_kinds.items())
        },
    }
    print(json.dumps(result, indent=2, sort_keys=True))
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
