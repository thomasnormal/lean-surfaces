#!/usr/bin/env python3
"""Reprice files blocked solely by ``TimedStatement:ImplicitEventControl``.

An implicit event control (``@*``/``@(*)``) computes a sensitivity set from
the statement's reads and then repeatedly re-enters the process.  This
read-only instrument reports the recovered body shapes while leaving
sensitivity inference and scheduler rearming loud.
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
WALL = "TimedStatement:ImplicitEventControl"
EVENT_RE = re.compile(r"@\s*(?:\*|\(\s*\*\s*\)|\([^)]*\))")


def walk(node):
    """Walk an envelope value, yielding dictionary nodes."""
    if isinstance(node, dict):
        yield node
        for value in node.values():
            yield from walk(value)
    elif isinstance(node, list):
        for value in node:
            yield from walk(value)


def implicit_features(text):
    """Return overlapping features recovered from one implicit-control span."""
    source = text.lower()
    labels = []
    if re.search(r"@\s*\(\s*\*\s*\)", source):
        labels.append("at-star-paren")
    else:
        labels.append("at-star-bare")
    patterns = (
        ("begin-block", r"\bbegin\b"),
        ("case", r"\bcase(?:z|x)?\s*\("),
        ("conditional", r"\bif\s*\("),
        ("for-loop", r"\bfor\s*\("),
        ("indexed-select", r"\[[^\]]+\]"),
        ("concat", r"\{[^{}]*[,}]"),
        ("system-call", r"\$[A-Za-z_]"),
        ("assignment", r"\b\w+\s*(?:<=|=)"),
    )
    labels.extend(label for label, pattern in patterns
                  if re.search(pattern, source))
    if len(EVENT_RE.findall(source)) > 1:
        labels.append("nested-control")
    return tuple(labels)


def one_file(path):
    """Return ``(status, feature tuples)`` for one corpus source."""
    data = path.read_bytes()
    text = data.decode("utf-8")
    if INCLUDE_RE.search(text):
        return "skip_include", []
    # Avoid invoking the frontend for the overwhelming majority of files that
    # cannot contain this timing-control spelling.
    if not re.search(r"@\s*(?:\*|\(\s*\*\s*\))", text):
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
    return "implicit_only", [implicit_features(node.get("text", ""))
                              for node in unsupported]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", required=True, type=pathlib.Path,
                        help="chapter-scoped sv-tests-2 tests directory")
    args = parser.parse_args(argv)

    files = sorted(args.corpus.glob("chapter-*/*.sv"))
    implicit_files = 0
    implicit_instances = 0
    features = collections.Counter()
    feature_files = collections.defaultdict(set)
    skipped = 0
    errors = 0

    for path in files:
        try:
            status, feature_sets = one_file(path)
        except Exception as exc:  # keep the measurement loud and complete
            print(f"error: {path}: {exc}", file=sys.stderr)
            errors += 1
            continue
        if status == "skip_include":
            skipped += 1
        elif status == "implicit_only":
            implicit_files += 1
            implicit_instances += len(feature_sets)
            for feature_set in feature_sets:
                for feature in feature_set:
                    features[feature] += 1
                    feature_files[feature].add(path.as_posix())

    result = {
        "corpus_files": len(files),
        "implicit_only_files": implicit_files,
        "implicit_instances": implicit_instances,
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
