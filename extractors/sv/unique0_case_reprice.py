#!/usr/bin/env python3
"""Reprice files blocked solely by ``CaseStatement:Unique0``.

Unique0 keeps first-match selection and checks overlapping matches, but unlike
unique it deliberately permits no matching item.  This read-only instrument
measures that distinction and the existing casez/casex/inside shapes without
inventing a diagnostic channel or case scheduler.
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
WALL = "CaseStatement:Unique0"


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


def unique0_features(statement, source, source_name=""):
    """Return overlapping source-shape labels for one unique0 case span."""
    text = _without_comments(statement.strip()).lower()
    name = source_name.lower()
    labels = ["unique0-case", "first-match", "no-match-allowed"]
    patterns = (
        ("casez", r"\bcasez\b"),
        ("casex", r"\bcasex\b"),
        ("inside", r"\binside\b"),
        ("default", r"\bdefault\s*:"),
        ("nonblocking", r"<="),
        ("indexed-select", r"\[[^\]]+\]"),
        ("multi-label", r"\b(?:[0-9a-z_'\"]+)\s*,\s*"
                        r"(?:[0-9a-z_'\"]+)\s*:"),
        ("wildcard-label", r"\?"),
    )
    labels.extend(label for label, pattern in patterns
                  if re.search(pattern, text, re.I))
    if "default" not in labels:
        labels.append("no-default")
    if "violation-when-multiple-match" in name:
        labels.append("multiple-match-violation")
    elif "no-violation" in name or "no-match-ok" in name:
        labels.append("no-match-no-violation")
    return tuple(labels)


def one_file(path):
    """Return ``(status, feature tuples)`` for one source file."""
    data = path.read_bytes()
    text = data.decode("utf-8")
    if INCLUDE_RE.search(text):
        return "skip_include", []
    if not re.search(r"\bunique0\s+case", text, re.I):
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
    return "unique0_only", [
        unique0_features(node.get("text", ""), text, path.name)
        for node in unsupported
    ]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", required=True, type=pathlib.Path,
                        help="chapter-scoped sv-tests-2 tests directory")
    args = parser.parse_args(argv)

    files = sorted(args.corpus.glob("chapter-*/*.sv"))
    unique0_files = 0
    unique0_instances = 0
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
        elif status == "unique0_only":
            unique0_files += 1
            unique0_instances += len(feature_sets)
            for feature_set in feature_sets:
                for feature in feature_set:
                    features[feature] += 1
                    feature_files[feature].add(path.as_posix())

    result = {
        "corpus_files": len(files),
        "unique0_only_files": unique0_files,
        "unique0_instances": unique0_instances,
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
