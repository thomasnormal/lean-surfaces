#!/usr/bin/env python3
"""Reprice files blocked solely by ``NetAliasSymbol:NetAlias``.

Net aliases create an elaboration-time bidirectional net relationship.  This
read-only instrument reports alias spelling and placement while leaving the
alias graph and resolved-driver behavior loud.
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
WALL = "NetAliasSymbol:NetAlias"


def walk(node):
    """Walk an envelope value, yielding dictionary nodes."""
    if isinstance(node, dict):
        yield node
        for value in node.values():
            yield from walk(value)
    elif isinstance(node, list):
        for value in node:
            yield from walk(value)


def alias_features(text):
    """Return source-span shape labels for one alias declaration."""
    source = text.lower()
    labels = []
    if len(re.findall(r"=", source)) >= 2:
        labels.append("chain")
    if re.search(r"\[[^\]]+\]", source):
        labels.append("indexed-select")
    return tuple(labels)


def one_file(path):
    """Return ``(status, alias feature tuples)`` for one source."""
    data = path.read_bytes()
    text = data.decode("utf-8")
    if INCLUDE_RE.search(text):
        return "skip_include", []
    if not re.search(r"\balias\b", text, re.I):
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
    features = [list(alias_features(span)) for span in spans]
    if len(spans) > 1:
        for feature_set in features:
            feature_set.append("multiple-statements")
    if re.search(r"\bgenerate\b|\bgenvar\b", text, re.I):
        for feature_set in features:
            feature_set.append("generate-placement")
    if re.search(r"`pragma\s+protect", text, re.I):
        for feature_set in features:
            feature_set.append("protected-region")
    return "alias_only", [tuple(dict.fromkeys(feature_set))
                           for feature_set in features]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", required=True, type=pathlib.Path,
                        help="chapter-scoped sv-tests-2 tests directory")
    args = parser.parse_args(argv)

    files = sorted(args.corpus.glob("chapter-*/*.sv"))
    alias_files = 0
    alias_instances = 0
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
        elif status == "alias_only":
            alias_files += 1
            alias_instances += len(feature_sets)
            for feature_set in feature_sets:
                for feature in feature_set:
                    features[feature] += 1
                    feature_files[feature].add(path.as_posix())

    result = {
        "corpus_files": len(files),
        "alias_only_files": alias_files,
        "alias_instances": alias_instances,
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
