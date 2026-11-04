#!/usr/bin/env python3
"""Reprice files blocked solely by ``NetSymbol:Tri0``.

``tri0`` supplies an implicit pull-0 driver to a resolved net.  This
read-only companion measures undriven, driven, strength and four-state cases
while leaving pull-driver resolution outside the legacy envelope.
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
WALL = "NetSymbol:Tri0"


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


def tri0_features(source):
    """Return overlapping driver and observation labels for one source."""
    source = _without_comments(source)
    labels = ["implicit-pull0"]
    assigns = re.findall(r"\bassign\b[^;]*;", source, re.I)
    if assigns:
        labels.append("continuous-driver")
    if any(re.search(r"\b(?:weak|strong|pull|highz)[01]?\b", item, re.I)
           for item in assigns):
        labels.append("explicit-strength")
    if re.search(r"\bassign\b\s+(?!\([^;]*\))[^;]*=\s*1\s*'\s*[bB]\s*1\b",
                 source, re.I):
        labels.append("strong-driver-overrides-pull")
    if re.search(r"\bassign\b[^;]*=\s*1\s*'\s*[bB]\s*[xX]\b", source,
                 re.I):
        labels.append("four-state-x-driver")
    if not assigns:
        labels.append("undriven-observation")
    return tuple(labels)


def one_file(path):
    """Return ``(status, feature tuples)`` for one source file."""
    data = path.read_bytes()
    text = data.decode("utf-8")
    if INCLUDE_RE.search(text):
        return "skip_include", []
    if not re.search(r"\btri0\b", text, re.I):
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
    return "tri0_only", [tri0_features(text) for _ in unsupported]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", required=True, type=pathlib.Path,
                        help="chapter-scoped sv-tests-2 tests directory")
    args = parser.parse_args(argv)

    files = sorted(args.corpus.glob("chapter-*/*.sv"))
    tri0_files = 0
    tri0_instances = 0
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
        elif status == "tri0_only":
            tri0_files += 1
            tri0_instances += len(feature_sets)
            for feature_set in feature_sets:
                for feature in feature_set:
                    features[feature] += 1
                    feature_files[feature].add(path.as_posix())

    result = {
        "corpus_files": len(files),
        "tri0_only_files": tri0_files,
        "tri0_instances": tri0_instances,
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
