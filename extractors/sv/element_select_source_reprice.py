#!/usr/bin/env python3
"""Reprice files blocked solely by ``ElementSelectExpression:source-type``."""

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
WALL = "ElementSelectExpression:source-type"


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


def selected_name(selection):
    match = re.match(
        r"\s*(?:[A-Za-z_$][A-Za-z0-9_$]*\.)*"
        r"([A-Za-z_$][A-Za-z0-9_$]*)\s*\[", selection or "")
    return match.group(1) if match else None


def element_features(text, selection):
    """Return overlapping source-shape labels for one unsupported select."""
    source = without_comments(text)
    lower = source.lower()
    name = selected_name(selection)
    if name is None:
        return ("unclassified-source",)

    # A packed union member can itself be a packed array.  Selecting one of
    # its elements needs the aggregate layout/aliasing state absent from the
    # legacy selected-read node.
    if re.search(r"\bunion\s+packed\b", lower) and re.search(
            r"\b" + re.escape(name.lower()) + r"\s*\[", lower):
        return ("packed-union-member",)

    # A scalar bit-select is a frontend legality diagnostic, not an array
    # access.  It has no unpacked declaration dimension after the name.
    declaration = re.search(
        r"\b(?:bit|logic|reg|wire)\b[^;{}]*\b" +
        re.escape(name) + r"\s*(?=;|=)", source, re.I)
    if declaration and not re.search(
            r"\b(?:bit|logic|reg|wire)\b[^;{}]*\b" +
            re.escape(name) + r"\s*\[", source, re.I):
        return ("scalar-source",)

    # Unpacked arrays have a dimension after the declared name.  OOB reads
    # retain the element's state kind; enum arrays additionally retain their
    # base-type default rule.
    unpacked = re.search(
        r"\b(?:bit|logic|reg|wire|[A-Za-z_$][A-Za-z0-9_$]*)\b[^;{}]*\b" +
        re.escape(name) + r"\s*\[", source, re.I)
    if unpacked:
        labels = ["unpacked-array-oob"]
        if re.search(r"\btypedef\s+enum\b", lower):
            labels.append("enum-base-default")
        elif re.search(r"\bbit\b[^;{}]*\b" + re.escape(name) +
                       r"\s*\[", source, re.I):
            labels.append("two-state-oob")
        else:
            labels.append("four-state-oob")
        return tuple(labels)

    return ("unclassified-source",)


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
    return "element_select_only", [
        element_features(text, node.get("text", "")) for node in unsupported
    ]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", required=True, type=pathlib.Path,
                        help="chapter-scoped sv-tests-2 tests directory")
    args = parser.parse_args(argv)
    selected_files = selected_spans = skipped = errors = 0
    features = collections.Counter()
    feature_files = collections.defaultdict(set)
    for path in sorted(args.corpus.glob("chapter-*/*.sv")):
        try:
            status, feature_sets = one_file(path)
        except Exception as exc:
            print(f"error: {path}: {exc}", file=sys.stderr)
            errors += 1
            continue
        if status == "skip_include":
            skipped += 1
        elif status == "element_select_only":
            selected_files += 1
            selected_spans += len(feature_sets)
            for feature_set in feature_sets:
                for feature in feature_set:
                    features[feature] += 1
                    feature_files[feature].add(path.as_posix())
    print(json.dumps({
        "corpus_files": len(list(args.corpus.glob("chapter-*/*.sv"))),
        "element_select_only_files": selected_files,
        "element_select_spans": selected_spans,
        "include_skips": skipped,
        "errors": errors,
        "features": {feature: {"spans": features[feature],
                               "files": len(feature_files[feature])}
                     for feature in sorted(features)},
    }, indent=2, sort_keys=True))
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
