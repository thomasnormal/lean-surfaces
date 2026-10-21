#!/usr/bin/env python3
"""Reprice files blocked solely by ``Hierarchy:module-kind``.

This read-only companion to ``census.py`` runs the extractor in process,
keeps only files whose complete Unsupported set is the non-module hierarchy
wall, and classifies every concrete program or interface instance in the
frontend tree.  Top-level non-module roots are included because they hit the
same boundary through module conversion; file counts overlap when a file has
several such instances.
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


def concrete_instances(instance):
    """Yield an instance and every concrete nested instance below it."""
    if symbol_kind(instance) == "Instance":
        yield instance
        for member in instance.body:
            yield from concrete_instances(member)
        return
    try:
        for member in instance:
            yield from concrete_instances(member)
    except TypeError:
        return


def definition_kind(instance):
    definition = getattr(getattr(instance, "body", None), "definition", None)
    value = getattr(definition, "definitionKind", None)
    if value is not None:
        return str(value).split(".")[-1]
    return "unknown"


def instance_shape(instance, top):
    """Return a stable source-independent shape for one non-module instance."""
    ports = list(getattr(instance.body, "portList", []) or [])
    connections = list(getattr(instance, "portConnections", []) or [])
    connection_kinds = tuple(
        "empty" if connection.expression is None
        else symbol_kind(connection.expression)
        for connection in connections
    )
    return {
        "kind": definition_kind(instance),
        "position": "top" if instance is top else "child",
        "ports": len(ports),
        "connections": connection_kinds,
    }


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
    if kinds != {"Hierarchy:module-kind"}:
        return "other", []

    shapes = []
    for top in compilation.getRoot().topInstances:
        for instance in concrete_instances(top):
            if not getattr(instance, "isModule", False):
                shapes.append(instance_shape(instance, top))
    return "module_kind_only", shapes


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", required=True, type=pathlib.Path,
                        help="chapter-scoped sv-tests-2 tests directory")
    args = parser.parse_args(argv)

    files = sorted(args.corpus.glob("chapter-*/*.sv"))
    kinds = collections.Counter()
    positions = collections.Counter()
    port_presence = collections.Counter()
    connection_expressions = collections.Counter()
    files_by_kind = collections.defaultdict(set)
    module_kind_files = 0
    instances = 0
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
        elif status == "module_kind_only":
            module_kind_files += 1
            for shape in shapes:
                instances += 1
                kind = shape["kind"]
                kinds[kind] += 1
                positions[shape["position"]] += 1
                port_presence["with_ports" if shape["ports"] else "portless"] += 1
                files_by_kind[kind].add(path.as_posix())
                for expression_kind in shape["connections"]:
                    connection_expressions[expression_kind] += 1

    result = {
        "corpus_files": len(files),
        "module_kind_only_files": module_kind_files,
        "instances": instances,
        "include_skips": skipped,
        "errors": errors,
        "kinds": {
            kind: {"instances": kinds[kind],
                   "files": len(files_by_kind[kind])}
            for kind in sorted(kinds)
        },
        "positions": dict(sorted(positions.items())),
        "port_presence": dict(sorted(port_presence.items())),
        "connection_expressions": dict(sorted(connection_expressions.items())),
    }
    print(json.dumps(result, indent=2, sort_keys=True))
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
