#!/usr/bin/env python3
"""Reprice files blocked solely by ``ClockingBlockSymbol:ClockingBlock``.

Clocking blocks sample and drive clockvars at scheduler-defined regions with
optional skew.  This read-only instrument reports declaration shapes while
leaving clockvar sampling, driving and region ordering loud.
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
WALL = "ClockingBlockSymbol:ClockingBlock"


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


def clocking_features(text):
    """Return overlapping source-shape labels for one clocking span."""
    source = _without_comments(text).lower()
    patterns = (
        ("global", r"\bglobal\s+clocking\b"),
        ("default", r"\bdefault\s+clocking\b"),
        ("input-clockvar", r"\binput\b"),
        ("output-clockvar", r"\boutput\b"),
        ("skew", r"\bdefault\s+input\s*#|\b(?:input|output)\s*#"),
        ("sequence-or-property", r"\b(?:sequence|property)\b"),
        ("nested-event", r"(?:@\s*\()[^@]*@\s*\("),
        ("nested-clocking", r"(?:\bclocking\s+\w+\b).*\bclocking\s+\w+\b"),
        ("end-label", r"\bendclocking\s*:"),
        ("unnamed", r"\bclocking\s*@"),
    )
    return tuple(label for label, pattern in patterns
                 if re.search(pattern, source, re.S))


def one_file(path):
    """Return ``(status, clocking feature tuples)`` for one source."""
    data = path.read_bytes()
    text = data.decode("utf-8")
    if INCLUDE_RE.search(text):
        return "skip_include", []
    if not re.search(r"\bclocking\b", text, re.I):
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
    features = [list(clocking_features(node.get("text", "")))
                for node in unsupported]
    if re.search(r"\bgenerate\b", text, re.I):
        for feature_set in features:
            feature_set.append("generate-placement")
    return "clocking_only", [tuple(dict.fromkeys(feature_set))
                             for feature_set in features]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", required=True, type=pathlib.Path,
                        help="chapter-scoped sv-tests-2 tests directory")
    args = parser.parse_args(argv)

    files = sorted(args.corpus.glob("chapter-*/*.sv"))
    clocking_files = 0
    clocking_instances = 0
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
        elif status == "clocking_only":
            clocking_files += 1
            clocking_instances += len(feature_sets)
            for feature_set in feature_sets:
                for feature in feature_set:
                    features[feature] += 1
                    feature_files[feature].add(path.as_posix())

    result = {
        "corpus_files": len(files),
        "clocking_only_files": clocking_files,
        "clocking_instances": clocking_instances,
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
