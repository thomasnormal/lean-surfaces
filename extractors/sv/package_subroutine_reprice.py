#!/usr/bin/env python3
"""Reprice files blocked solely by ``Package:Subroutine``."""

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
WALL = "Package:Subroutine"


def walk(node):
    if isinstance(node, dict):
        yield node
        for value in node.values():
            yield from walk(value)
    elif isinstance(node, list):
        for value in node:
            yield from walk(value)


def without_comments(text):
    text = re.sub(r"/\*.*?\*/", " ", text, flags=re.S)
    return re.sub(r"//[^\n]*", " ", text)


def subroutine_features(text, declaration):
    """Return overlapping package-subroutine source-shape labels."""
    source = without_comments(text)
    stripped = declaration.strip()
    if re.match(r'import\s+["\']DPI-C["\']\s+(?:context\s+)?function\b',
                stripped, re.I):
        return ("dpi-import",)
    name_match = re.search(
        r"\bfunction\b(?:\s+automatic)?(?:\s+\w+)*\s+"
        r"([A-Za-z_$][A-Za-z0-9_$]*)\s*\(", stripped, re.I)
    if not name_match:
        return ("unclassified-subroutine",)
    name = name_match.group(1)
    labels = ["package-function"]
    # The declaration contributes one spelling; additional calls identify a
    # constant-function use in a localparam or generate elaboration context.
    calls = re.findall(r"\b" + re.escape(name) + r"\s*\(", source)
    if len(calls) > 1:
        labels.append("constant-function-use")
    else:
        labels.append("nonconstant-function")
    return tuple(labels)


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
    if kinds != {WALL}:
        return "other", []
    return "package_subroutine_only", [
        subroutine_features(text, node.get("text", ""))
        for node in unsupported
    ]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", required=True, type=pathlib.Path,
                        help="chapter-scoped sv-tests-2 tests directory")
    args = parser.parse_args(argv)
    paths = sorted(args.corpus.glob("chapter-*/*.sv"))
    selected_files = selected_spans = skipped = errors = 0
    features = collections.Counter()
    feature_files = collections.defaultdict(set)
    for path in paths:
        try:
            status, feature_sets = one_file(path)
        except Exception as exc:
            print(f"error: {path}: {exc}", file=sys.stderr)
            errors += 1
            continue
        if status == "skip_include":
            skipped += 1
        elif status == "package_subroutine_only":
            selected_files += 1
            selected_spans += len(feature_sets)
            for feature_set in feature_sets:
                for feature in feature_set:
                    features[feature] += 1
                    feature_files[feature].add(path.as_posix())
    print(json.dumps({
        "corpus_files": len(paths),
        "package_subroutine_only_files": selected_files,
        "package_subroutine_spans": selected_spans,
        "include_skips": skipped,
        "errors": errors,
        "features": {feature: {"spans": features[feature],
                               "files": len(feature_files[feature])}
                     for feature in sorted(features)},
    }, indent=2, sort_keys=True))
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
