#!/usr/bin/env python3
"""Reprice files blocked solely by ``Package:invalid-compilation``.

This is a design-level diagnostic boundary.  The read-only instrument reports
the package timeunit/import/export shapes that lead to a frontend rejection;
it never salvages a partial package or changes elaboration.
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
WALL = "Package:invalid-compilation"


def walk(node):
    """Walk an envelope value, yielding dictionary nodes."""
    if isinstance(node, dict):
        yield node
        for value in node.values():
            yield from walk(value)
    elif isinstance(node, list):
        for value in node:
            yield from walk(value)


def _without_comments(text):
    text = re.sub(r"/\*.*?\*/", " ", text, flags=re.S)
    return re.sub(r"//[^\n]*", " ", text)


def package_invalid_features(text):
    """Return overlapping source-shape labels for one rejected package."""
    source = _without_comments(text).lower()
    labels = []
    if len(re.findall(r"\btimeunit\b", source)) >= 2:
        labels.append("repeated-timeunit")
    has_import = bool(re.search(r"\bimport\b", source))
    has_export = bool(re.search(r"\bexport\b", source))
    if has_import:
        labels.append("import")
    if len(re.findall(r"\bimport\b", source)) >= 2:
        labels.append("multiple-imports")
    if re.search(r"\bimport\s+\w+\s*::\s*\*", source):
        labels.append("wildcard-import")
    if has_export:
        labels.append("export")
    if has_import and has_export:
        labels.append("import-export")
    if re.search(r"\bexport\s*\*\s*::\s*\*", source):
        labels.append("star-export")
    if has_export and not has_import:
        labels.append("export-without-import")
    return tuple(labels)


def one_file(path):
    """Return ``(status, invalid-package feature tuples)`` for one source."""
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
    return "invalid_only", [package_invalid_features(text)
                             for _ in unsupported]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", required=True, type=pathlib.Path,
                        help="chapter-scoped sv-tests-2 tests directory")
    args = parser.parse_args(argv)

    files = sorted(args.corpus.glob("chapter-*/*.sv"))
    invalid_files = 0
    invalid_instances = 0
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
        elif status == "invalid_only":
            invalid_files += 1
            invalid_instances += len(feature_sets)
            for feature_set in feature_sets:
                for feature in feature_set:
                    features[feature] += 1
                    feature_files[feature].add(path.as_posix())

    result = {
        "corpus_files": len(files),
        "invalid_only_files": invalid_files,
        "invalid_instances": invalid_instances,
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
