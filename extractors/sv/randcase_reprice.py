#!/usr/bin/env python3
"""Reprice files blocked solely by ``RandCaseStatement``.

``randcase`` selects one branch according to evaluated integral weights.  This
read-only instrument reports weight and body shapes without choosing a branch
or introducing a random source into the extractor.
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
WALL = "RandCaseStatement"


def walk(node):
    """Walk an envelope value, yielding dictionary nodes."""
    if isinstance(node, dict):
        yield node
        for value in node.values():
            yield from walk(value)
    elif isinstance(node, list):
        for value in node:
            yield from walk(value)


def randcase_features(text):
    """Return overlapping features recovered from one randcase span."""
    source = text.lower()
    patterns = (
        ("zero-weight", r"\b0\s*:"),
        ("branch-block", r"\bbegin\b"),
        ("indexed-target", r"\[[^\]]+\]"),
        ("increment", r"\+\+|--"),
    )
    labels = [label for label, pattern in patterns
              if re.search(pattern, source)]
    weights = []
    expression_weight = False
    # Split source clauses at statement separators so an expression such as
    # ``w + 1`` is distinguished from an integral literal weight.  The
    # source slice can be truncated, so this is deliberately shape telemetry,
    # not a parser for the full randcase grammar.
    for clause in re.split(r"[;\n]", source):
        if ":" not in clause:
            continue
        weight = clause.split(":", 1)[0].strip()
        weight = re.sub(r"^randcase\b", "", weight).strip()
        if re.fullmatch(r"[+-]?\d+", weight):
            weights.append(int(weight))
        elif weight:
            expression_weight = True
    if expression_weight:
        labels.append("weight-expression")
    # A randcase with no positive numeric weight is a distinct diagnostic
    # obligation from a branch that merely has one zero-weight arm.
    if len(weights) > 1 and all(value == 0 for value in weights):
        labels.append("all-zero-weight")
    return tuple(dict.fromkeys(labels))


def one_file(path):
    """Return ``(status, feature tuples)`` for one corpus source."""
    data = path.read_bytes()
    text = data.decode("utf-8")
    if INCLUDE_RE.search(text):
        return "skip_include", []
    if not re.search(r"\brandcase\b", text, re.I):
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
    return "randcase_only", [randcase_features(node.get("text", ""))
                              for node in unsupported]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", required=True, type=pathlib.Path,
                        help="chapter-scoped sv-tests-2 tests directory")
    args = parser.parse_args(argv)

    files = sorted(args.corpus.glob("chapter-*/*.sv"))
    randcase_files = 0
    randcase_instances = 0
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
        elif status == "randcase_only":
            randcase_files += 1
            randcase_instances += len(feature_sets)
            for feature_set in feature_sets:
                for feature in feature_set:
                    features[feature] += 1
                    feature_files[feature].add(path.as_posix())

    result = {
        "corpus_files": len(files),
        "randcase_only_files": randcase_files,
        "randcase_instances": randcase_instances,
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
