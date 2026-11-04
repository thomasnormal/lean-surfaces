#!/usr/bin/env python3
"""Reprice files blocked solely by ``GenericClassDefSymbol``.

Parameterized classes bind value/type parameters before class members and
specializations are selected.  This read-only instrument reports those
source shapes without elaborating a specialization or inventing a class
object model.
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
WALL = "GenericClassDefSymbol"


def walk(node):
    """Walk an envelope value, yielding dictionary nodes."""
    if isinstance(node, dict):
        yield node
        for value in node.values():
            yield from walk(value)
    elif isinstance(node, list):
        for value in node:
            yield from walk(value)


def generic_features(text):
    """Return overlapping source-feature labels for one generic class span."""
    source = text.lower()
    patterns = (
        ("virtual", r"\bvirtual\s+class\b"),
        ("value-parameters", r"#\s*\(.*\bparameter\s+(?!type\b)"),
        ("type-parameters", r"#\s*\(.*\bparameter\s+type\b"),
        ("typedef-members", r"\btypedef\b"),
        ("local-parameters", r"\blocalparam\b"),
        ("static-methods", r"\bstatic\s+(?:function|task)\b"),
        ("packed-aggregate-types", r"\bstruct\s+packed\b|\bunion\s+packed\b"),
    )
    return tuple(label for label, pattern in patterns
                 if re.search(pattern, source, re.S))


def one_file(path):
    """Return ``(status, generic feature tuples)`` for one source."""
    data = path.read_bytes()
    text = data.decode("utf-8")
    if INCLUDE_RE.search(text):
        return "skip_include", []
    # A source without the class keyword cannot contain this class marker;
    # avoid invoking the frontend for the common non-class corpus rows.
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
    return "generic_class_only", [generic_features(node.get("text", ""))
                                   for node in unsupported]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", required=True, type=pathlib.Path,
                        help="chapter-scoped sv-tests-2 tests directory")
    args = parser.parse_args(argv)

    files = sorted(args.corpus.glob("chapter-*/*.sv"))
    generic_files = 0
    generic_instances = 0
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
        elif status == "generic_class_only":
            generic_files += 1
            generic_instances += len(feature_sets)
            for feature_set in feature_sets:
                for feature in feature_set:
                    features[feature] += 1
                    feature_files[feature].add(path.as_posix())

    result = {
        "corpus_files": len(files),
        "generic_class_only_files": generic_files,
        "generic_class_instances": generic_instances,
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
