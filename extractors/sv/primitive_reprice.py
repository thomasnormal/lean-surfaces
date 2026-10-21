#!/usr/bin/env python3
"""Reprice files blocked solely by ``PrimitiveInstanceSymbol:PrimitiveInstance``.

This read-only companion to ``census.py`` runs extraction in process, keeps
only files whose complete Unsupported set is a primitive-instance wall, and
groups the concrete frontend primitive instances by their IEEE primitive
family.  No primitive is admitted by rewriting it as a pure expression: the
instrument measures the driver shapes that a future scheduler-facing rung
would have to represent.
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


def primitive_instances(instance):
    """Yield concrete primitive instances below one top instance."""
    if symbol_kind(instance) == "PrimitiveInstance":
        yield instance
    if symbol_kind(instance) == "Instance":
        members = instance.body
    else:
        try:
            members = iter(instance)
        except TypeError:
            return
    for member in members:
        yield from primitive_instances(member)


def primitive_name(instance):
    """Read the frontend's primitive enum without depending on enum order."""
    value = str(getattr(instance, "primitiveType", ""))
    match = re.search(r'"([^"]+)"', value)
    return match.group(1) if match else value.split(".")[-1]


def primitive_group(name):
    if name in {"and", "or", "xor", "xnor", "nand", "nor", "not", "buf"}:
        return "logic gate"
    if name in {"bufif0", "bufif1", "notif0", "notif1"}:
        return "conditional gate"
    if name in {"nmos", "pmos", "cmos", "rcmos", "rnmos", "rpmos"}:
        return "MOS switch"
    if name in {"tran", "tranif0", "tranif1", "rtran", "rtranif0", "rtranif1"}:
        return "tran switch"
    if name in {"pullup", "pulldown"}:
        return "pull source"
    return "other primitive"


def instance_shape(instance):
    name = primitive_name(instance)
    return {
        "primitive": name,
        "group": primitive_group(name),
        "delay": getattr(instance, "delay", None) is not None,
        "array": getattr(instance, "arrayName", None) is not None,
        "connections": len(getattr(instance, "portConnections", []) or []),
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
    if kinds != {"PrimitiveInstanceSymbol:PrimitiveInstance"}:
        return "other", []

    shapes = []
    for top in compilation.getRoot().topInstances:
        shapes.extend(instance_shape(instance)
                      for instance in primitive_instances(top))
    return "primitive_only", shapes


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", required=True, type=pathlib.Path,
                        help="chapter-scoped sv-tests-2 tests directory")
    args = parser.parse_args(argv)

    files = sorted(args.corpus.glob("chapter-*/*.sv"))
    primitives = collections.Counter()
    groups = collections.Counter()
    files_by_primitive = collections.defaultdict(set)
    delays = collections.Counter()
    arrays = collections.Counter()
    arities = collections.Counter()
    primitive_files = 0
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
        elif status == "primitive_only":
            primitive_files += 1
            for shape in shapes:
                instances += 1
                name = shape["primitive"]
                primitives[name] += 1
                groups[shape["group"]] += 1
                files_by_primitive[name].add(path.as_posix())
                delays["with_delay" if shape["delay"] else "without_delay"] += 1
                arrays["array" if shape["array"] else "scalar"] += 1
                arities[str(shape["connections"])] += 1

    result = {
        "corpus_files": len(files),
        "primitive_only_files": primitive_files,
        "primitive_instances": instances,
        "include_skips": skipped,
        "errors": errors,
        "primitives": {
            name: {"instances": primitives[name],
                   "files": len(files_by_primitive[name])}
            for name in sorted(primitives)
        },
        "groups": dict(sorted(groups.items())),
        "delays": dict(sorted(delays.items())),
        "arrays": dict(sorted(arrays.items())),
        "connection_arities": dict(sorted(arities.items())),
    }
    print(json.dumps(result, indent=2, sort_keys=True))
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
