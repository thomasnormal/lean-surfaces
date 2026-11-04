#!/usr/bin/env python3
"""Reprice files blocked solely by ``TimedStatement:DelayControl:expression``.

This read-only instrument reports delay-expression shapes.  It does not turn
dynamic, real or unit-scaled controls into fixed delays.
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
WALL = "TimedStatement:DelayControl:expression"


def walk(node):
    """Walk an envelope value, yielding dictionary nodes."""
    if isinstance(node, dict):
        yield node
        for value in node.values():
            yield from walk(value)
    elif isinstance(node, list):
        for value in node:
            yield from walk(value)


def delay_expression_features(text, context="", path=""):
    """Return overlapping source-shape labels for one delay expression."""
    statement = text.strip()
    lower = (context or "").lower()
    labels = ["delay-expression"]

    # Unit-bearing time literals are distinct from an unqualified fixed-point
    # delay because their conversion uses the active timeunit/precision.
    if re.search(r"#\s*[0-9]+(?:\.[0-9]+)?[ \t]*(?:s|ms|us|ns|ps|fs)\b",
                 statement, re.I):
        labels.append("unit-suffixed")
    if re.search(r"#\s*[0-9]+\.[0-9]+", statement):
        labels.append("fixed-point")
    if re.search(r"#\s*(?:\([^)]*[A-Za-z_$][^)]*\)|[A-Za-z_$][\w$]*)",
                 statement):
        labels.append("dynamic-reference")
    expr = statement.split("#", 1)[1] if "#" in statement else statement
    if re.search(r"[+*/%-]", expr):
        labels.append("arithmetic-expression")
    if re.search(r"unknown|high.?impedance|x.?or.?z|x.?becomes.?zero|treated as zero|zero delay",
                 lower):
        labels.append("x-z-zero")
    if re.search(r"timescale|timeunit|timeprecision|precision|round(?:ed|ing)|scaled",
                 lower):
        labels.append("time-scale-precision")
    if re.search(r"#\s*(?:\([^)]*\)|[A-Za-z_$][\w$]*|[0-9]+(?:\.[0-9]+)?)\s+[A-Za-z_$][\w$]*\s*=",
                 statement):
        labels.append("delay-before-assignment")
    if re.search(r"parameter", lower) or re.search(r"#\s*[A-Za-z_$][\w$]*", statement):
        labels.append("parameter-or-signal")
    if "/chapter-20/" in path or "/chapter-22/" in path:
        labels.append("time-query-context")
    return tuple(dict.fromkeys(labels))


def one_file(path):
    """Return ``(status, feature tuples)`` for one source file."""
    data = path.read_bytes()
    text = data.decode("utf-8")
    if INCLUDE_RE.search(text):
        return "skip_include", []
    if not re.search(r"#", text):
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
    return "delay_expression_only", [
        delay_expression_features(node.get("text", ""), text,
                                  path.as_posix())
        for node in unsupported
    ]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", required=True, type=pathlib.Path,
                        help="chapter-scoped sv-tests-2 tests directory")
    args = parser.parse_args(argv)

    files = sorted(args.corpus.glob("chapter-*/*.sv"))
    delay_files = 0
    delay_instances = 0
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
        elif status == "delay_expression_only":
            delay_files += 1
            delay_instances += len(feature_sets)
            for feature_set in feature_sets:
                for feature in feature_set:
                    features[feature] += 1
                    feature_files[feature].add(path.as_posix())

    result = {
        "corpus_files": len(files),
        "delay_expression_only_files": delay_files,
        "delay_expression_instances": delay_instances,
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
