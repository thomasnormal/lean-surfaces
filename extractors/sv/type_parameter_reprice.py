#!/usr/bin/env python3
"""Reprice files blocked solely by ``TypeParameterSymbol:TypeParameter``.

Type parameters affect elaboration-time type identity and every declaration or
expression that depends on the selected type.  This read-only instrument
reports source-span shapes and keeps type binding and overrides loud.
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
WALL = "TypeParameterSymbol:TypeParameter"


def walk(node):
    """Walk an envelope value, yielding dictionary nodes."""
    if isinstance(node, dict):
        yield node
        for value in node.values():
            yield from walk(value)
    elif isinstance(node, list):
        for value in node:
            yield from walk(value)


def type_parameter_features(text):
    """Return overlapping source-feature labels for one type-parameter span."""
    source = text.lower()
    if not source:
        return ("empty-span",)
    patterns = (
        ("type-operator", r"\btype\s*\("),
        ("typed-default", r"=\s*(?:int|shortint|byte|logic|bit|integer)\b"),
        ("type-dependent-value", r"\b(?:parameter|localparam)\b.*\btype\b|\btype\b.*="),
    )
    return tuple(label for label, pattern in patterns
                 if re.search(pattern, source, re.S))


def one_file(path):
    """Return ``(status, type-parameter feature tuples)`` for one source."""
    data = path.read_bytes()
    text = data.decode("utf-8")
    if INCLUDE_RE.search(text):
        return "skip_include", []
    if not re.search(r"\b(?:parameter\s+type|localparam\s+type)\b|#\s*\([^)]*\btype\b|\btype\s+\w+\s*=", text, re.S):
        return "other", []
    tree = SyntaxTree.fromText(text, name=path.as_posix())
    compilation = Compilation()
    compilation.addSyntaxTree(tree)
    extract._SOURCE_BYTES = data
    envelope = extract.convert_design(tree.sourceManager, compilation)
    unsupported = [node for node in walk(envelope)
                   if node.get("kind") == "Unsupported"]
    kinds = {node.get("sv_kind") for node in unsupported}
    if kinds != {WALL}:
        return "other", []
    return "type_parameter_only", [type_parameter_features(node.get("text", ""))
                                    for node in unsupported]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", required=True, type=pathlib.Path,
                        help="chapter-scoped sv-tests-2 tests directory")
    args = parser.parse_args(argv)

    files = sorted(args.corpus.glob("chapter-*/*.sv"))
    type_files = 0
    type_instances = 0
    features = collections.Counter()
    feature_files = collections.defaultdict(set)
    skipped = 0
    errors = 0

    for path in files:
        try:
            status, feature_sets = one_file(path)
        except Exception as exc:
            print(f"error: {path}: {exc}", file=sys.stderr)
            errors += 1
            continue
        if status == "skip_include":
            skipped += 1
        elif status == "type_parameter_only":
            type_files += 1
            type_instances += len(feature_sets)
            for feature_set in feature_sets:
                for feature in feature_set:
                    features[feature] += 1
                    feature_files[feature].add(path.as_posix())

    result = {
        "corpus_files": len(files),
        "type_parameter_only_files": type_files,
        "type_parameter_instances": type_instances,
        "include_skips": skipped,
        "errors": errors,
        "features": {
            feature: {"instances": features[feature],
                      "files": len(feature_files[feature])}
            for feature in sorted(features)
        },
    }
    print(json.dumps(result, indent=2, sort_keys=True))
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
