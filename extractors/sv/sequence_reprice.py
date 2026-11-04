#!/usr/bin/env python3
"""Reprice files blocked solely by ``SequenceSymbol:Sequence``.

Concurrent sequence declarations carry sampled clocks, temporal operators,
local/formal scope and endpoint state.  This read-only instrument reports
those source shapes without evaluating a sequence or adding an assertion
automaton.
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
WALL = "SequenceSymbol:Sequence"


def walk(node):
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


def sequence_features(text):
    """Return overlapping IEEE sequence-shape labels."""
    source = _without_comments(text)
    lower = source.lower()
    labels = []
    if re.search(r"\bint\s+\w+|\blocal\s+(?:int|\w+)", lower):
        labels.append("local-variable")
    if re.search(r"\bsequence\s+\w+\s*\(\s*[^)]", lower):
        labels.append("formal-argument")
    if len(re.findall(r"@\s*\(\s*posedge\s+", lower)) >= 2:
        labels.append("multiclock")
    if re.search(r"\bintersect\b", lower):
        labels.append("intersect")
    if re.search(r"##\s*[0-9]", lower):
        labels.append("temporal-concatenation")
    if re.search(r"\.matched\b", lower):
        labels.append("matched-endpoint")
    if re.search(r"endsequence\s*:\s*\w+", lower):
        labels.append("end-label")
    if re.search(r"\bevent\s+\w+|@\s*\(\s*\w+\s*\)", lower):
        labels.append("event-local-diagnostic")
    if re.search(r"\bsequence\s+\w+\s*\(\s*sequence\b", lower):
        labels.append("sequence-typed-formal")
    if re.search(r"\$rose\b|\$fell\b|\$past\b|\$stable\b", lower):
        labels.append("sampled-value")
    return tuple(dict.fromkeys(labels))


def one_file(path):
    data = path.read_bytes()
    text = data.decode("utf-8")
    if INCLUDE_RE.search(text):
        return "skip_include", []
    if not re.search(r"\bsequence\b", text, re.I):
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
    return "sequence_only", [sequence_features(text) for _ in unsupported]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", required=True, type=pathlib.Path,
                        help="chapter-scoped sv-tests-2 tests directory")
    args = parser.parse_args(argv)
    files = sorted(args.corpus.glob("chapter-*/*.sv"))
    sequence_files = 0
    sequence_instances = 0
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
        elif status == "sequence_only":
            sequence_files += 1
            sequence_instances += len(feature_sets)
            for feature_set in feature_sets:
                for feature in feature_set:
                    features[feature] += 1
                    feature_files[feature].add(path.as_posix())
    result = {
        "corpus_files": len(files),
        "sequence_only_files": sequence_files,
        "sequence_instances": sequence_instances,
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
