#!/usr/bin/env python3
"""Reprice files blocked solely by ``ConditionalStatement:Priority``.

Priority-if evaluates its conditions in listed order, selects the first true
branch, and reports a no-match violation when the chain has no explicit
fallback.  This read-only instrument measures those source shapes without
erasing the qualifier or adding a diagnostic/scheduler model.
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
WALL = "ConditionalStatement:Priority"


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


def priority_if_features(statement, source, source_name=""):
    """Return overlapping source-shape labels for one priority-if span."""
    text = _without_comments(statement.strip()).lower()
    whole = _without_comments(source).lower()
    name = source_name.lower()
    labels = ["priority-if", "first-match", "listed-order"]
    if re.search(r"\belse\s+if\b", text, re.I):
        labels.append("condition-chain")
    if (len(re.findall(r"[<>]", text)) >= 2
            or "&&" in text
            or any(marker in name for marker in
                   ("evaluates-in-listed-order", "first-true-selected",
                    "first-true-wins"))):
        labels.append("multiple-true")
    final_else = r"\belse(?!\s+if\b)\s+(?:begin\b|[^;{}\n]+;)"
    invalid = bool(re.search(r"\belse\s+priority(?:0|\s+if)?\b",
                             whole, re.I))
    if re.search(final_else, text, re.I) and not invalid:
        labels.append("explicit-else")
    elif not invalid:
        labels.append("no-match-path")
    if re.search(r"\[[^\]]+\]", text, re.I):
        labels.append("indexed-select")
    if re.search(r"\balways_comb\b", whole, re.I):
        labels.append("always-comb-context")
    elif re.search(r"\balways\b", whole, re.I):
        labels.append("always-context")
    if "no-match-no-else" in name:
        labels.append("no-match-violation")
    if invalid:
        labels.append("invalid-after-else")
    return tuple(labels)


def one_file(path):
    """Return ``(status, feature tuples)`` for one source file."""
    data = path.read_bytes()
    text = data.decode("utf-8")
    if INCLUDE_RE.search(text):
        return "skip_include", []
    if not re.search(r"\bpriority\s+if\b", text, re.I):
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
    return "priority_if_only", [
        priority_if_features(node.get("text", ""), text, path.name)
        for node in unsupported
    ]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", required=True, type=pathlib.Path,
                        help="chapter-scoped sv-tests-2 tests directory")
    args = parser.parse_args(argv)

    files = sorted(args.corpus.glob("chapter-*/*.sv"))
    priority_files = 0
    priority_instances = 0
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
        elif status == "priority_if_only":
            priority_files += 1
            priority_instances += len(feature_sets)
            for feature_set in feature_sets:
                for feature in feature_set:
                    features[feature] += 1
                    feature_files[feature].add(path.as_posix())

    result = {
        "corpus_files": len(files),
        "priority_if_only_files": priority_files,
        "priority_if_instances": priority_instances,
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
