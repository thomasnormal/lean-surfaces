#!/usr/bin/env python3
"""Reprice files blocked solely by ``NetSymbol:TriReg``.

``trireg`` is a charge-storage net rather than an ordinary resolved wire.
This read-only companion measures the declaration and driver shapes in the
sole-wall files.  It never turns a capacitive net into a procedural variable
or chooses a charge-decay rule for the existing scheduler.
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
WALL = "NetSymbol:TriReg"


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


def _declaration_text(source, span):
    """Return the declaration containing an unsupported symbol span."""
    lines = source.splitlines()
    index = max(0, int(span.get("line", 1)) - 1)
    start = index
    while start > 0 and "trireg" not in lines[start].lower():
        start -= 1
    end = index
    while end + 1 < len(lines) and ";" not in lines[end]:
        end += 1
    return " ".join(lines[start:end + 1])


def trireg_features(declaration, source):
    """Return overlapping source-shape labels for one trireg declaration."""
    declaration = _without_comments(declaration)
    source = _without_comments(source)
    labels = []

    if re.search(r"\btrireg\s*\(\s*(?:small|medium|large)\b",
                 declaration, re.I):
        labels.append("charge-strength")
    if re.search(r"\btrireg\b[^;\n]*#\s*\(", declaration, re.I):
        labels.append("charge-decay-delay")
    if re.search(r"\btrireg\b[^;\n]*\[[^\]]+\]", declaration, re.I):
        labels.append("packed-vector")
    if re.search(r"\btrireg_(?:la|sm)\b", declaration, re.I):
        labels.append("capacitive-network")

    # The source-level driver shapes apply to every concrete trireg declaration
    # in a file.  The labels deliberately describe observations and state that
    # a future driver representation would have to preserve.
    if re.search(r"1\s*'\s*[bB]\s*[zZ]|driver\s+goes\s+[zZ]|\bdisconnect",
                 source, re.I):
        labels.append("driver-release")
    if re.search(r"\b(?:undriven|initially\s+[xXzZ]|starts\s+"
                 r"(?:simulation\s+)?with\s+[xXzZ])\b", source, re.I):
        labels.append("undriven-startup")
    if re.search(r"1\s*'\s*[bB]\s*[xX]|===\s*1\s*'\s*[bB]\s*[xX]|"
                 r"!==\s*1\s*'\s*[bB]\s*[xX]|\bx\s+driver\b",
                 source, re.I):
        labels.append("four-state-x")
    if re.search(r"\b(?:capacitive|retain|charge)\b", source, re.I):
        labels.append("capacitive-state")
    return tuple(labels)


def one_file(path):
    """Return ``(status, feature tuples)`` for one source file."""
    data = path.read_bytes()
    text = data.decode("utf-8")
    if INCLUDE_RE.search(text):
        return "skip_include", []
    if not re.search(r"\btrireg\b", text, re.I):
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
    return "trireg_only", [
        trireg_features(_declaration_text(text, node.get("span", {})), text)
        for node in unsupported
    ]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", required=True, type=pathlib.Path,
                        help="chapter-scoped sv-tests-2 tests directory")
    args = parser.parse_args(argv)

    files = sorted(args.corpus.glob("chapter-*/*.sv"))
    trireg_files = 0
    trireg_instances = 0
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
        elif status == "trireg_only":
            trireg_files += 1
            trireg_instances += len(feature_sets)
            for feature_set in feature_sets:
                for feature in feature_set:
                    features[feature] += 1
                    feature_files[feature].add(path.as_posix())

    result = {
        "corpus_files": len(files),
        "trireg_only_files": trireg_files,
        "trireg_instances": trireg_instances,
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
