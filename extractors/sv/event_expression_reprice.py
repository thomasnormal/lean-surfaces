#!/usr/bin/env python3
"""Reprice files blocked solely by ``SignalEventControl:clock``.

Event controls over expressions retain a sampled value and re-arm when that
value changes.  This read-only instrument reports expression shapes while
leaving event registration and wake-up semantics loud.
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
WALL = "SignalEventControl:clock"


def walk(node):
    """Walk an envelope value, yielding dictionary nodes."""
    if isinstance(node, dict):
        yield node
        for value in node.values():
            yield from walk(value)
    elif isinstance(node, list):
        for value in node:
            yield from walk(value)


def event_expression_features(text, context="", path=""):
    """Return overlapping source-shape labels for one event expression."""
    statement = text.strip()
    source = re.sub(r"/\*.*?\*/", " ", context or "", flags=re.S)
    source = re.sub(r"//[^\n]*", " ", source)
    lower = (context or "").lower()
    labels = []
    if re.search(r"\b(?:posedge|negedge|edge)\b", statement, re.I):
        labels.append("edge-event")
        if re.search(r"@(\s*\b(?:posedge|negedge|edge)\s+[^)]*\[[^]]+\])",
                     statement, re.I):
            labels.append("selected-edge")
        elif re.search(r"@\(\s*\b(?:posedge|negedge|edge)\s+[^)]*\b(?:bus|vec|sig)\b",
                       statement, re.I):
            labels.append("multibit-lsb-edge")
    else:
        labels.append("value-change-event")
    if re.search(r"\[[^]]+\]", statement):
        labels.append("select-expression")
    if re.search(r"@\s*\(\s*\{", statement):
        labels.append("concat-expression")
    if re.search(r"@\s*\(\s*[^()]+\?", statement):
        labels.append("conditional-expression")
    if re.search(r"@\s*\(\s*\([^)]*\s[&|^]\s*[^)]*\)", statement):
        labels.append("binary-expression")
    if re.search(r"@\s*\(\s*[^()]*\s[&|^]\s*[^()]*\)", statement):
        labels.append("binary-expression")
    if re.search(r"@\s*\(\s*[&|^~]", statement):
        labels.append("reduction-or-unary-expression")
    if re.search(r"result|operand|expression result|no event|any change",
                 lower):
        labels.append("result-change-filter")
    if re.search(r"singular|aggregate|array", lower):
        labels.append("singular-or-aggregate")
    if "/chapter-4/" in path:
        labels.append("scheduler-context")
    return tuple(dict.fromkeys(labels))


def one_file(path):
    """Return ``(status, feature tuples)`` for one source file."""
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
        return "event_expression_only", []
    return "event_expression_only", [
        event_expression_features(node.get("text", ""), text,
                                  path.as_posix())
        for node in unsupported
    ]


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
        elif feature_sets:
            event_files += 1
            event_instances += len(feature_sets)
            for feature_set in feature_sets:
                for feature in feature_set:
                    features[feature] += 1
                    feature_files[feature].add(path.as_posix())

    result = {
        "corpus_files": len(files),
        "event_expression_only_files": event_files,
        "event_expression_instances": event_instances,
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
