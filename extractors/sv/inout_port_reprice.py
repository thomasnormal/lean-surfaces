#!/usr/bin/env python3
"""Reprice files blocked solely by ``PortSymbol:InOut``."""

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
WALL = "PortSymbol:InOut"


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


def inout_features(text, declaration):
    """Return overlapping source-shape labels for one unsupported port."""
    source = without_comments(text)
    lower = source.lower()
    labels = []
    if re.search(r"\binterconnect\b", lower):
        if re.search(r"=\s*[^,;)]", declaration):
            labels.append("interconnect-initializer")
        elif re.search(r"\bsigned\b", lower):
            labels.append("interconnect-signed")
        else:
            labels.append("interconnect-port")
        return tuple(labels)

    if re.search(r"\binterface\b[^;]*;", lower):
        labels.append("generic-interface-nonansi")
        return tuple(labels)

    if re.search(r"=\s*[^,;)]", declaration):
        labels.append("inout-initializer")
    if re.search(r"\bwire\s+x\s*,\s*y\s*\[[^]]+\]", lower):
        labels.append("unpacked-dimension-not-inherited")
    if re.search(r"\binteger\s+x\s*,\s*signed\s*\[[^]]+\]\s*y", lower):
        labels.append("integer-then-signed-type-reset")
    if re.search(r"\[[^]]+\]\s*x\s*,\s*wire\s+y", lower):
        labels.append("packed-dimension-then-wire-reset")
    return tuple(labels) or ("inout-net-port",)


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
    return "inout_only", [
        inout_features(text, node.get("text", "")) for node in unsupported
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
        elif status == "inout_only":
            selected_files += 1
            selected_spans += len(feature_sets)
            for feature_set in feature_sets:
                for feature in feature_set:
                    features[feature] += 1
                    feature_files[feature].add(path.as_posix())
    print(json.dumps({
        "corpus_files": len(paths),
        "inout_only_files": selected_files,
        "inout_spans": selected_spans,
        "include_skips": skipped,
        "errors": errors,
        "features": {feature: {"spans": features[feature],
                               "files": len(feature_files[feature])}
                     for feature in sorted(features)},
    }, indent=2, sort_keys=True))
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
