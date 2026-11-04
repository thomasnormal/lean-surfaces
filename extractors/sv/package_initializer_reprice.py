#!/usr/bin/env python3
"""Reprice files blocked solely by ``Package:initializer``.

Package variable initializers run before simulation processes and can depend on
package/import visibility.  This read-only instrument reports those source
shapes while leaving dependency ordering and initialization state loud.
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
WALL = "Package:initializer"


def walk(node):
    """Walk an envelope value, yielding dictionary nodes."""
    if isinstance(node, dict):
        yield node
        for value in node.values():
            yield from walk(value)
    elif isinstance(node, list):
        for value in node:
            yield from walk(value)


def package_initializer_features(text):
    """Return overlapping source-shape labels for one initializer."""
    source = text.lower()
    rhs = source.split("=", 1)[1] if "=" in source else ""
    labels = []
    if re.search(r"\b[a-z_]\w*\b", rhs):
        labels.append("runtime-reference")
    if "::" in rhs:
        labels.append("qualified-reference")
    if re.search(r"[+*/%-]", rhs):
        labels.append("arithmetic")
    if len(re.findall(r"\b[a-z_]\w*\b", rhs)) >= 2:
        labels.append("multiple-identifiers")
    return tuple(labels)


def one_file(path):
    """Return ``(status, initializer feature tuples)`` for one source."""
    data = path.read_bytes()
    text = data.decode("utf-8")
    if INCLUDE_RE.search(text):
        return "skip_include", []
    if not re.search(r"\bpackage\b", text, re.I):
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
    spans = [node.get("text", "") for node in unsupported]
    features = [list(package_initializer_features(span)) for span in spans]
    if len(spans) > 1:
        for feature_set in features:
            feature_set.append("multiple-initializers")
    if re.search(r"\bexport\b", text, re.I):
        for feature_set in features:
            feature_set.append("export-context")
    if re.search(r"\bexport\s*\*\s*::\s*\*", text, re.I):
        for feature_set in features:
            feature_set.append("wildcard-export")
    return "initializer_only", [tuple(dict.fromkeys(feature_set))
                                for feature_set in features]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", required=True, type=pathlib.Path,
                        help="chapter-scoped sv-tests-2 tests directory")
    args = parser.parse_args(argv)

    files = sorted(args.corpus.glob("chapter-*/*.sv"))
    initializer_files = 0
    initializer_instances = 0
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
        elif status == "initializer_only":
            initializer_files += 1
            initializer_instances += len(feature_sets)
            for feature_set in feature_sets:
                for feature in feature_set:
                    features[feature] += 1
                    feature_files[feature].add(path.as_posix())

    result = {
        "corpus_files": len(files),
        "initializer_only_files": initializer_files,
        "initializer_instances": initializer_instances,
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
