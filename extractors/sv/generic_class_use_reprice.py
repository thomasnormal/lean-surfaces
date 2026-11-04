#!/usr/bin/env python3
"""Reprice files blocked solely by ``GenericClassDefSymbol:GenericClassDef``.

This marker is distinct from the generic declaration marker: it records a
parameterized class body whose member/scope elaboration remains unsupported.
The instrument reports source features only and never performs specialization
or class-scope lookup.
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
WALL = "GenericClassDefSymbol:GenericClassDef"


def walk(node):
    """Walk an envelope value, yielding dictionary nodes."""
    if isinstance(node, dict):
        yield node
        for value in node.values():
            yield from walk(value)
    elif isinstance(node, list):
        for value in node:
            yield from walk(value)


def generic_use_features(text):
    """Return overlapping source-feature labels for one generic class body."""
    source = text.lower()
    patterns = (
        ("value-parameter-member", r"\bparameter\s+(?!type\b)"),
        ("type-parameter-member", r"\b(?:parameter\s+)?type\s+\w+"),
        ("local-parameter-member", r"\blocalparam\b"),
        ("class-scope-resolution", r"::"),
        ("member-typedef", r"\btypedef\b"),
    )
    return tuple(label for label, pattern in patterns
                 if re.search(pattern, source))


def one_file(path):
    """Return ``(status, generic-use feature tuples)`` for one source."""
    data = path.read_bytes()
    text = data.decode("utf-8")
    if INCLUDE_RE.search(text):
        return "skip_include", []
    if not re.search(r"\bclass\b[^;{}\n]*#\s*\(", text):
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
    return "generic_class_use_only", [generic_use_features(node.get("text", ""))
                                       for node in unsupported]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", required=True, type=pathlib.Path,
                        help="chapter-scoped sv-tests-2 tests directory")
    args = parser.parse_args(argv)

    files = sorted(args.corpus.glob("chapter-*/*.sv"))
    use_files = 0
    use_instances = 0
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
        elif status == "generic_class_use_only":
            use_files += 1
            use_instances += len(feature_sets)
            for feature_set in feature_sets:
                for feature in feature_set:
                    features[feature] += 1
                    feature_files[feature].add(path.as_posix())

    result = {
        "corpus_files": len(files),
        "generic_class_use_only_files": use_files,
        "generic_class_use_instances": use_instances,
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
