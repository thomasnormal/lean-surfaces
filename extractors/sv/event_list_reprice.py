#!/usr/bin/env python3
"""Reprice files blocked solely by ``TimedStatement:EventListControl``.

Event lists wake a process from any of several event expressions, optionally
with edge and ``iff`` filters.  This read-only instrument reports list shapes
while leaving multi-registration and rearming semantics loud.
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
WALL = "TimedStatement:EventListControl"


def walk(node):
    """Walk an envelope value, yielding dictionary nodes."""
    if isinstance(node, dict):
        yield node
        for value in node.values():
            yield from walk(value)
    elif isinstance(node, list):
        for value in node:
            yield from walk(value)


def event_list_features(text):
    """Return overlapping event-list shape labels for one span."""
    source = text.lower()
    patterns = (
        ("or-list", r"\bor\b"),
        ("comma-list", r","),
        ("edge-event", r"\b(?:posedge|negedge|edge)\b"),
        ("iff-filter", r"\biff\b"),
        ("parenthesized-list", r"@\s*\(\s*\("),
        ("always-ff", r"\balways_ff\b"),
        ("block-body", r"\bbegin\b"),
        ("procedural-assign", r"\b(?:assign|deassign)\b"),
        ("indexed-expression", r"\[[^\]]+\]"),
    )
    labels = [label for label, pattern in patterns
              if re.search(pattern, source)]
    if len(re.findall(r"\b(?:or|,)", source)) >= 2:
        labels.append("three-or-more-events")
    return tuple(labels)


def one_file(path):
    """Return ``(status, event-list feature tuples)`` for one source."""
    data = path.read_bytes()
    text = data.decode("utf-8")
    if INCLUDE_RE.search(text):
        return "skip_include", []
    if not re.search(r"@\s*\(", text):
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
    return "event_list_only", [event_list_features(node.get("text", ""))
                                for node in unsupported]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", required=True, type=pathlib.Path,
                        help="chapter-scoped sv-tests-2 tests directory")
    args = parser.parse_args(argv)

    files = sorted(args.corpus.glob("chapter-*/*.sv"))
    event_files = 0
    event_instances = 0
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
        elif status == "event_list_only":
            event_files += 1
            event_instances += len(feature_sets)
            for feature_set in feature_sets:
                for feature in feature_set:
                    features[feature] += 1
                    feature_files[feature].add(path.as_posix())

    result = {
        "corpus_files": len(files),
        "event_list_only_files": event_files,
        "event_list_instances": event_instances,
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
