#!/usr/bin/env python3
"""Reprice files blocked solely by ``EmptyMemberSymbol:EmptyMember``."""

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
WALL = "EmptyMemberSymbol:EmptyMember"


def walk(node):
    if isinstance(node, dict):
        yield node
        for value in node.values():
            yield from walk(value)
    elif isinstance(node, list):
        for value in node:
            yield from walk(value)


def empty_member_features(text):
    """Return source-shape labels for a frontend empty-member marker."""
    source = re.sub(r"/\*.*?\*/", " ", text, flags=re.S)
    source = re.sub(r"//[^\n]*", " ", source).lower()
    if re.search(r"`begin_keywords\s+\"1800-2012\"", source):
        return ("soft-keyword-under-begin-keywords",)
    if re.search(r"\b(?:and|or|xor|xnor|nand|nor|buf|not)\s*\[[^]]+\]\s*\(", source):
        return ("primitive-array-without-instance-name",)
    if re.search(r"\(\*[^*]*=\s*\(\*", source, re.S):
        return ("nested-attribute-expression",)
    if re.search(r"\b(?:integer|int|logic|reg|wire)\s+\$[a-z_$]", source):
        return ("dollar-leading-simple-identifier",)
    return ("other-empty-member",)


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
    return "empty_member_only", [empty_member_features(text)
                                  for _ in unsupported]


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
        elif status == "empty_member_only":
            selected_files += 1
            selected_spans += len(feature_sets)
            for feature_set in feature_sets:
                for feature in feature_set:
                    features[feature] += 1
                    feature_files[feature].add(path.as_posix())
    print(json.dumps({
        "corpus_files": len(paths),
        "empty_member_only_files": selected_files,
        "empty_member_spans": selected_spans,
        "include_skips": skipped,
        "errors": errors,
        "features": {feature: {"spans": features[feature],
                               "files": len(feature_files[feature])}
                     for feature in sorted(features)},
    }, indent=2, sort_keys=True))
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
