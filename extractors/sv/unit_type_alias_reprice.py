#!/usr/bin/env python3
"""Reprice files blocked solely by ``TypeAliasType`` (unit aliases)."""

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
WALL = "TypeAliasType"


def walk(node):
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


def unit_alias_features(text):
    """Return overlapping aggregate/union shape labels."""
    source = _without_comments(text)
    lower = source.lower()
    labels = []
    if re.search(r"\bvirtual\s+\w+\s+\w+", lower) \
            or re.search(r"\b(?:real|string)\s+\w+", lower):
        labels.append("nonintegral-packed-member")
    if re.search(r"\bunion\s+packed\b[\s\S]*\b(?:bit|logic)\s*\[[^]]+\]",
                 lower):
        widths = re.findall(r"\b(?:bit|logic)\s*\[([^]]+)\]", lower)
        if len(widths) >= 2 and len(set(widths)) > 1:
            labels.append("packed-union-width")
    if re.search(r"\b(?:struct|union)\s*\[[^]]+\]", lower):
        labels.append("packed-dimension-qualifier")
    if re.search(r"\bstruct\s+signed\b", lower):
        labels.append("unpacked-struct-signing")
    if re.search(r"\bunion\s*\{[\s\S]*=\s*'\{", lower):
        labels.append("union-member-default")
    if re.search(r"\bunion\s*\{[\s\S]*\bvoid\s+\w+", lower):
        labels.append("void-in-untagged-union")
    if re.search(r"\bunion\s+tagged\s+packed\b", lower):
        labels.append("packed-tagged-union")
    if re.search(r"\bunion\s+tagged\b[\s\S]*\bstring\s+\w+", lower):
        labels.append("tagged-union-dynamic-member")
    if re.search(r"\bunion\s*\{[\s\S]*\bstring\s+\w+", lower):
        labels.append("untagged-union-dynamic-member")
    return tuple(dict.fromkeys(labels))


def one_file(path):
    data = path.read_bytes()
    text = data.decode("utf-8")
    if INCLUDE_RE.search(text):
        return "skip_include", []
    if not re.search(r"\btypedef\b", text, re.I):
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
    return "unit_alias_only", [unit_alias_features(text) for _ in unsupported]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", required=True, type=pathlib.Path,
                        help="chapter-scoped sv-tests-2 tests directory")
    args = parser.parse_args(argv)
    files = sorted(args.corpus.glob("chapter-*/*.sv"))
    alias_files = alias_instances = skipped = errors = 0
    features = collections.Counter()
    feature_files = collections.defaultdict(set)
    for path in files:
        try:
            status, feature_sets = one_file(path)
        except Exception as exc:
            print(f"error: {path}: {exc}", file=sys.stderr)
            errors += 1
            continue
        if status == "skip_include":
            skipped += 1
        elif status == "unit_alias_only":
            alias_files += 1
            alias_instances += len(feature_sets)
            for feature_set in feature_sets:
                for feature in feature_set:
                    features[feature] += 1
                    feature_files[feature].add(path.as_posix())
    print(json.dumps({
        "corpus_files": len(files), "unit_alias_only_files": alias_files,
        "unit_alias_instances": alias_instances, "include_skips": skipped,
        "errors": errors,
        "features": {feature: {"instances": features[feature],
                                "files": len(feature_files[feature])}
                     for feature in sorted(features)},
    }, indent=2, sort_keys=True))
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
